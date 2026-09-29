#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ARÈNE — Console de surveillance EDGE01   (OUTIL FORMATEUR — NE PAS DISTRIBUER)
=============================================================================

Console web autonome (Python stdlib pur, zéro dépendance) : tour de contrôle de
la machine cible PARTAGÉE du lab. Elle écoute tout, cible par personne / IP / MAC,
agit en direct (ralentir, geler, bannir, geler une session), et enregistre le
journal complet sur disque.

Écoute :
  - SSH        : journal systemd -> échecs / réussites / users invalides par IP
  - HTTP/HTTPS : nginx access.log -> chemins, codes
  - SMB / SNMP : connexions vivantes (ss)
  - sudo/su    : journal -> tentatives d'élévation (COMMAND=/usr/bin/find …) -> ALERTE
  - Système    : CPU, mémoire, disque, charge, uptime, services, ports en écoute
  - Sessions   : qui est connecté, depuis quelle IP  ->  ciblage "par personne"
  - MAC        : table ARP (ip neigh)

Agit (par IP) :
  - Ralentir   : perte de paquets (~65%) -> l'attaque rame
  - Geler      : DROP total (bascule manuelle)
  - Bannir     : DROP total avec durée + levée automatique
  - Geler la session d'une personne connectée : SIGSTOP de ses process (+ réveil)

Enregistre :
  - chaque événement -> journal JSONL horodaté sur disque (rotation par jour)
  - téléchargement du journal + export de l'état depuis l'UI

Accès :
  - PAGE DE LOGIN par jeton (cookie de session ; plus de jeton dans l'URL)

Modes :
  python3 arene_console.py                         # sur EDGE01 (root) : RÉEL, écoute LOOPBACK (127.0.0.1)
                                                   #   -> jeton fort généré + affiché au démarrage
                                                   #   -> se voit du poste formateur par tunnel SSH (ProxyJump)
  python3 arene_console.py --demo                  # ailleurs : données fictives, actions simulées
"""

import argparse
import atexit
import http.cookies
import ipaddress
import json
import os
import random
import re
import secrets
import signal
import socket
import subprocess
import sys
import threading
import time
from collections import deque
from hmac import compare_digest
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

try:
    import pwd                       # Unix seulement (absent sous Windows / mode --demo)
except ImportError:
    pwd = None

# --------------------------------------------------------------------------- #
NGINX_ACCESS = "/var/log/nginx/access.log"
PORT_SERVICE = {22: "SSH", 80: "HTTP", 443: "HTTPS", 8080: "HTTP-8080",
                445: "SMB", 139: "SMB", 161: "SNMP"}
WATCH_SERVICES = ["ssh", "nginx", "smbd", "snmpd"]
SLOW_PROBABILITY = "0.65"
SNAPSHOT_EVERY = 3.0
SYSTEM_EVERY = 4.0
MAX_EVENTS = 800
MAX_BODY = 65536                # borne du corps POST (anti-DoS)
IPS_CAP = 3000                  # plafond du nombre d'IP suivies (anti-croissance mémoire)
# marqueurs d'élévation dans une commande sudo -> alerte rouge
PRIVESC_HINTS = ("find", "/bin/sh", "/bin/bash", "vim", "vi ", "less", "more",
                 "nmap", "awk", "perl", "python", "tar", "env ", "man ")

# --------------------------------------------------------------------------- #
LOCK = threading.RLock()
STOP = threading.Event()
IPS = {}
EVENTS = deque(maxlen=MAX_EVENTS)
SUDO_EVENTS = deque(maxlen=200)
BLOCKS = {}                    # ip -> {"type": ban|freeze|slow, "until": epoch|None, "at": epoch}
FROZEN_USERS = set()           # sessions gelées (SIGSTOP)
SYSTEM = {}                    # instantané système
SESSION_BY_IP = {}             # ip -> user connecté
PREV_CONNS = set()
SELF_IPS = set()
SAFE_IPS = set()
STATE = {"demo": False, "started": time.time(), "record": None}
_CPU_PREV = [None]


def now():
    return time.time()


def log(msg):
    sys.stderr.write("[arene] %s\n" % msg)
    sys.stderr.flush()


# --------------------------------------------------------------------------- #
# Enregistrement sur disque (JSONL, rotation par jour)                        #
# --------------------------------------------------------------------------- #
_REC = {"day": None, "fh": None, "dir": None}


def record_event(e):
    d = _REC["dir"]
    if not d:
        return
    try:
        day = time.strftime("%Y%m%d")
        if day != _REC["day"]:
            if _REC["fh"]:
                _REC["fh"].close()
            os.makedirs(d, exist_ok=True)
            _REC["fh"] = open(os.path.join(d, "arene-%s.jsonl" % day), "a", encoding="utf-8")
            _REC["day"] = day
        _REC["fh"].write(json.dumps(e, ensure_ascii=False) + "\n")
        _REC["fh"].flush()
    except Exception:
        pass


# --------------------------------------------------------------------------- #
# Modèle par IP                                                               #
# --------------------------------------------------------------------------- #
def ip_rec(ip):
    r = IPS.get(ip)
    if r is None:
        r = {
            "ip": ip, "mac": None, "first": now(), "last": now(),
            "ssh": {"fail": 0, "ok": 0, "invalid": 0, "users": {}},
            "http": {"req": 0, "paths": {}, "last_status": None},
            "smb": {"conn": 0}, "snmp": {"hits": 0},
            "live": [], "events": deque(maxlen=40),
        }
        IPS[ip] = r
        if len(IPS) > IPS_CAP:                    # éviction des plus anciennes sans blocage actif
            old = sorted((k for k in IPS if k not in BLOCKS and k != ip),
                         key=lambda k: IPS[k]["last"])
            for k in old[:len(IPS) - IPS_CAP]:
                IPS.pop(k, None)
    return r


def push_event(ip, service, level, detail):
    e = {"ts": now(), "ip": ip, "service": service, "level": level, "detail": detail}
    with LOCK:                                   # protège EVENTS + IPS (RLock réentrant)
        EVENTS.append(e)
        if ip and ip != "-":                     # "-" = événement système, pas une IP source
            ip_rec(ip)["events"].append(e)
    record_event(e)


def _bump(d, key, cap):
    if key is None:
        return
    d[key] = d.get(key, 0) + 1
    if len(d) > cap:
        smallest = min(d, key=d.get)
        if smallest != key:
            d.pop(smallest, None)


def note_ssh(ip, kind, user):
    with LOCK:
        r = ip_rec(ip); r["last"] = now(); s = r["ssh"]
        if kind == "ok":
            s["ok"] += 1; push_event(ip, "SSH", "ok", "login REUSSI (%s)" % user)
        elif kind == "invalid":
            s["invalid"] += 1; s["fail"] += 1
            push_event(ip, "SSH", "warn", "user invalide (%s)" % user)
        else:
            s["fail"] += 1; push_event(ip, "SSH", "fail", "echec mot de passe (%s)" % user)
        _bump(s["users"], user, 60)


def note_http(ip, method, path, status):
    with LOCK:
        r = ip_rec(ip); r["last"] = now(); h = r["http"]
        h["req"] += 1; h["last_status"] = status
        _bump(h["paths"], "%s %s" % (method, path), 80)
        lvl = "fail" if (status and status >= 500) else ("warn" if (status and status >= 400) else "info")
        push_event(ip, "HTTP", lvl, "%s %s %s" % (status, method, path))


def note_conn(ip, service):
    with LOCK:
        r = ip_rec(ip); r["last"] = now()
        if service == "SMB":
            r["smb"]["conn"] += 1; push_event(ip, "SMB", "info", "connexion SMB")
        elif service == "SNMP":
            r["snmp"]["hits"] += 1; push_event(ip, "SNMP", "info", "requete SNMP")


def note_sudo(user, command, ip=None):
    with LOCK:
        privesc = any(h in command for h in PRIVESC_HINTS)
        e = {"ts": now(), "user": user, "command": command[:200],
             "ip": ip, "privesc": privesc}
        SUDO_EVENTS.append(e)
        rec = {"ts": e["ts"], "ip": ip or "-", "service": "SUDO",
               "level": "fail" if privesc else "warn",
               "detail": "%s : sudo %s" % (user, command[:120])}
        EVENTS.append(rec); record_event(rec)
        if ip:
            ip_rec(ip)["events"].append(rec)


# --------------------------------------------------------------------------- #
# Parsers                                                                     #
# --------------------------------------------------------------------------- #
_IP = r"(\d{1,3}(?:\.\d{1,3}){3})"
RE_SSH_OK = re.compile(r"Accepted \S+ for (\S+) from " + _IP)   # \S+ : couvre keyboard-interactive/pam, publickey…
RE_SSH_INV = re.compile(r"Invalid user (\S+) from " + _IP)
RE_SSH_FAIL = re.compile(r"Failed password for (?!invalid user)(\S+) from " + _IP)
RE_NGINX = re.compile(r'^(\S+)\s+\S+\s+\S+\s+\[[^\]]+\]\s+"(\S+)\s+([^"\s]+)[^"]*"\s+(\d{3})')  # (\S+) : IPv4 ET IPv6
RE_SUDO = re.compile(r"^\s*(\S+)\s*:.*COMMAND=(.+?)\s*$")


def parse_ssh_line(line):
    m = RE_SSH_OK.search(line)
    if m:
        note_ssh(m.group(2), "ok", m.group(1)); return
    m = RE_SSH_INV.search(line)
    if m:
        note_ssh(m.group(2), "invalid", m.group(1)); return
    m = RE_SSH_FAIL.search(line)
    if m:
        note_ssh(m.group(2), "fail", m.group(1)); return


def parse_nginx_line(line):
    m = RE_NGINX.match(line)
    if m:
        try:
            note_http(m.group(1), m.group(2), m.group(3), int(m.group(4)))
        except ValueError:
            pass


_SUDO_DENY = ("NOT in sudoers", "incorrect password", "authentication failure",
              "command not allowed", "not allowed to execute", "a password is required")


def parse_sudo_line(line):
    if any(k in line for k in _SUDO_DENY):        # tentative REFUSÉE/échec : pas une exécution
        return
    m = RE_SUDO.match(line)
    if m:
        user = m.group(1)
        with LOCK:
            ip = None
            for sip, suser in SESSION_BY_IP.items():
                if suser == user:
                    ip = sip; break
        note_sudo(user, m.group(2), ip)


# --------------------------------------------------------------------------- #
# Collecte                                                                    #
# --------------------------------------------------------------------------- #
def run(argv):
    try:
        return subprocess.run(argv, capture_output=True, text=True, timeout=5).stdout
    except Exception:
        return ""


def stream_cmd(argv, handler, name):
    while not STOP.is_set():
        try:
            p = subprocess.Popen(argv, stdout=subprocess.PIPE,
                                 stderr=subprocess.DEVNULL, text=True, bufsize=1)
        except FileNotFoundError:
            log("flux '%s' desactive (%s absent)" % (name, argv[0])); return
        except Exception as e:
            log("flux '%s' erreur: %s" % (name, e)); time.sleep(3); continue
        try:
            for line in p.stdout:
                if STOP.is_set():
                    break
                try:
                    handler(line.rstrip("\n"))
                except Exception:
                    pass
        finally:
            try:
                p.terminate()
            except Exception:
                pass
        if STOP.is_set():
            return
        time.sleep(2)


def snapshot_loop():
    global PREV_CONNS
    while not STOP.is_set():
        try:
            macs = {}
            for line in run(["ip", "-o", "neigh"]).splitlines():
                f = line.split()
                if len(f) >= 5 and f[0].count(".") == 3 and "lladdr" in f:
                    macs[f[0]] = f[f.index("lladdr") + 1]
            live = {}
            cur = set()
            for line in run(["ss", "-Hant", "state", "established"]).splitlines():
                f = line.split()
                if len(f) < 5:
                    continue
                try:
                    lport = int(f[3].rsplit(":", 1)[-1])
                except ValueError:
                    continue
                svc = PORT_SERVICE.get(lport)
                if not svc:
                    continue
                pm = re.search(_IP, f[4])
                if not pm:
                    continue
                pip = pm.group(1)
                if pip in SELF_IPS or pip.startswith("127."):
                    continue
                live.setdefault(pip, set()).add(svc)
                cur.add((pip, lport))
            with LOCK:
                for r in IPS.values():
                    r["live"] = []
                for pip, svcs in live.items():
                    r = ip_rec(pip); r["live"] = sorted(svcs); r["last"] = now()
                for pip, port in (cur - PREV_CONNS):
                    svc = PORT_SERVICE.get(port)
                    if svc == "SMB":
                        note_conn(pip, "SMB")
                    elif svc == "SNMP":
                        note_conn(pip, "SNMP")
                for ip, mac in macs.items():
                    if ip in IPS:
                        IPS[ip]["mac"] = mac
                PREV_CONNS = cur
        except Exception as e:
            log("snapshot: %s" % e)
        STOP.wait(SNAPSHOT_EVERY)


def cpu_percent():
    try:
        with open("/proc/stat") as f:
            vals = list(map(int, f.readline().split()[1:]))
        idle = vals[3] + (vals[4] if len(vals) > 4 else 0)
        total = sum(vals)
        prev = _CPU_PREV[0]
        _CPU_PREV[0] = (total, idle)
        if prev is None or total <= prev[0]:
            return None
        return round(100.0 * ((total - prev[0]) - (idle - prev[1])) / (total - prev[0]), 1)
    except Exception:
        return None


def read_system():
    d = {"ts": now()}
    try:
        d["load"] = open("/proc/loadavg").read().split()[:3]
    except Exception:
        d["load"] = None
    try:
        mi = {}
        for line in open("/proc/meminfo"):
            k, _, v = line.partition(":")
            mi[k] = int(v.split()[0])
        d["mem_total"] = mi.get("MemTotal", 0)
        d["mem_avail"] = mi.get("MemAvailable", mi.get("MemFree", 0))
    except Exception:
        d["mem_total"] = d["mem_avail"] = 0
    try:
        d["uptime"] = float(open("/proc/uptime").read().split()[0])
    except Exception:
        d["uptime"] = 0
    try:
        s = os.statvfs("/")
        d["disk_total"] = s.f_blocks * s.f_frsize
        d["disk_free"] = s.f_bavail * s.f_frsize
    except Exception:
        d["disk_total"] = d["disk_free"] = 0
    d["cpu"] = cpu_percent()
    d["services"] = {u: (run(["systemctl", "is-active", u]).strip() or "?") for u in WATCH_SERVICES}
    ports = set()
    for line in (run(["ss", "-Hltn"]) + run(["ss", "-Hlun"])).splitlines():
        f = line.split()
        if len(f) >= 4:
            m = re.search(r":(\d+)$", f[3])
            if m:
                ports.add(int(m.group(1)))
    d["listen"] = sorted(ports)
    # sessions (who)
    sess = []
    by_ip = {}
    for line in run(["who"]).splitlines():
        m = re.match(r"^(\S+)\s+(\S+)\s+(\d{4}-\d\d-\d\d \d\d:\d\d)(?:\s+\(([^)]+)\))?", line)
        if not m:
            continue
        ipm = re.search(_IP, m.group(4) or "")
        sip = ipm.group(1) if ipm else None
        sess.append({"user": m.group(1), "tty": m.group(2), "since": m.group(3),
                     "ip": sip, "frozen": m.group(1) in FROZEN_USERS})
        if sip:
            by_ip[sip] = m.group(1)
    d["sessions"] = sess
    with LOCK:
        SESSION_BY_IP.clear()
        SESSION_BY_IP.update(by_ip)
    return d


def system_loop():
    while not STOP.is_set():
        try:
            s = read_system()
            with LOCK:
                SYSTEM.clear(); SYSTEM.update(s)
        except Exception as e:
            log("system: %s" % e)
        STOP.wait(SYSTEM_EVERY)


def ban_expiry_loop():
    while not STOP.is_set():
        with LOCK:
            expired = [ip for ip, b in BLOCKS.items() if b.get("until") and now() >= b["until"]]
        for ip in expired:
            clear_block(ip, reason="expiration")
        STOP.wait(5)


# --------------------------------------------------------------------------- #
# Actions                                                                     #
# --------------------------------------------------------------------------- #
def _rule_args(ip, btype):
    if btype == "slow":
        return ["-s", ip, "-m", "statistic", "--mode", "random",
                "--probability", SLOW_PROBABILITY, "-j", "DROP"]
    return ["-s", ip, "-j", "DROP"]


def _iptables(action, ip, btype):
    subprocess.run(["iptables", "-w", action, "INPUT", *_rule_args(ip, btype)],
                   check=True, capture_output=True, timeout=8)


def apply_block(ip, btype, minutes):
    ipaddress.ip_address(ip)
    if ip in SELF_IPS or ip in SAFE_IPS or ip.startswith("127."):
        raise ValueError("IP protegee (locale/formateur)")
    if btype not in ("ban", "freeze", "slow"):
        raise ValueError("type inconnu")
    minutes = int(minutes)
    with LOCK:
        old = BLOCKS.get(ip)
    if old and not STATE["demo"]:
        try:
            _iptables("-D", ip, old["type"])
        except Exception:
            pass
    if not STATE["demo"]:
        _iptables("-I", ip, btype)
    with LOCK:
        BLOCKS[ip] = {"type": btype, "until": now() + minutes * 60 if minutes > 0 else None, "at": now()}
    labels = {"ban": "banni", "freeze": "gele", "slow": "ralenti"}
    push_event(ip, "ACTION", "fail", labels[btype] + (" %d min" % minutes if minutes > 0 else ""))


def clear_block(ip, reason="manuel"):
    ipaddress.ip_address(ip)
    with LOCK:
        b = BLOCKS.get(ip)
    if b and not STATE["demo"]:
        for _ in range(6):                        # -D en boucle : retire toutes les copies de la règle
            r = subprocess.run(["iptables", "-w", "-D", "INPUT", *_rule_args(ip, b["type"])],
                               capture_output=True, text=True, timeout=8)
            if r.returncode != 0:                 # plus de règle correspondante -> terminé
                break
    with LOCK:
        BLOCKS.pop(ip, None)
    push_event(ip, "ACTION", "ok", "relache (%s)" % reason)


def freeze_session(ip):
    with LOCK:
        user = SESSION_BY_IP.get(ip)
    if not user:
        raise ValueError("aucune session connectee depuis cette IP")
    _freeze_user(user, ip)


def _freeze_user(user, ip=None):
    if pwd is not None and not STATE["demo"]:
        try:
            if pwd.getpwnam(user).pw_uid < 1000:
                raise ValueError("compte systeme protege")
        except KeyError:
            raise ValueError("utilisateur inconnu")
    if not STATE["demo"]:
        subprocess.run(["pkill", "-STOP", "-u", user], capture_output=True, timeout=5)
    with LOCK:
        FROZEN_USERS.add(user)
    push_event(ip or "-", "ACTION", "fail", "session GELEE : %s (SIGSTOP)" % user)


def wake_user(user):
    if not STATE["demo"]:
        subprocess.run(["pkill", "-CONT", "-u", user], capture_output=True, timeout=5)
    with LOCK:
        FROZEN_USERS.discard(user)
    push_event("-", "ACTION", "ok", "session reveillee : %s (SIGCONT)" % user)


_CLEANED = [False]


def cleanup():
    if _CLEANED[0]:
        return
    _CLEANED[0] = True
    STOP.set()
    with LOCK:
        ips = list(BLOCKS.keys()); users = list(FROZEN_USERS)
    for ip in ips:
        try:
            clear_block(ip, reason="arret")
        except Exception:
            pass
    for u in users:
        try:
            wake_user(u)
        except Exception:
            pass
    if _REC["fh"]:
        try:
            _REC["fh"].close()
        except Exception:
            pass


# --------------------------------------------------------------------------- #
# Démo                                                                        #
# --------------------------------------------------------------------------- #
def demo_loop():
    students = [("172.16.34.%d" % (50 + i),
                 "bc:24:11:%02x:%02x:%02x" % (i, (i * 7) % 255, (i * 13) % 255))
                for i in range(1, 13)]
    users = ["root", "admin", "p.durand", "l.fontaine", "m.petit", "s.meyer",
             "k.benali", "j.moreau", "test", "oracle", "administrator"]
    ok_users = {"p.durand", "l.fontaine", "m.petit"}
    bad_users = {"root", "admin", "test", "oracle", "j.moreau", "administrator"}
    good_paths = ["/", "/robots.txt", "/backup/", "/backup/notes.txt", "/portail-rh-old/",
                  "/.env.example", "/uploads/", "/backup/config.php.bak", "/equipe.html"]
    paths = good_paths + ["/admin/", "/monitoring/", "/dev", "/old-site"]
    footholds = [("172.16.34.51", "p.durand"), ("172.16.34.53", "l.fontaine")]
    with LOCK:
        for ip, mac in students:
            ip_rec(ip)["mac"] = mac
        SYSTEM.update({
            "ts": now(), "load": ["0.42", "0.51", "0.48"], "cpu": 17.0,
            "mem_total": 2048000, "mem_avail": 1200000, "uptime": 8640,
            "disk_total": 20 * 10**9, "disk_free": 14 * 10**9,
            "services": {s: "active" for s in WATCH_SERVICES},
            "listen": [22, 80, 139, 161, 443, 445, 8080, 8899],
            "sessions": [{"user": u, "tty": "pts/%d" % i, "since": "2026-09-29 10:1%d" % i,
                          "ip": ip, "frozen": False} for i, (ip, u) in enumerate(footholds)],
        })
        SESSION_BY_IP.update({ip: u for ip, u in footholds})
    while not STOP.is_set():
        ip, _ = random.choice(students)
        roll = random.random()
        if roll < 0.45:
            u = random.choice(users)
            if u in ok_users and random.random() < 0.12:
                note_ssh(ip, "ok", u)
            elif u in bad_users:
                note_ssh(ip, "invalid", u)
            else:
                note_ssh(ip, "fail", u)
        elif roll < 0.8:
            p = random.choice(paths)
            st = 200 if p in good_paths else (403 if p == "/monitoring/" else 404)
            note_http(ip, "GET", p, st)
        elif roll < 0.93:
            note_conn(ip, "SMB" if random.random() < 0.8 else "SNMP")
        else:
            fip, fuser = random.choice(footholds)
            note_sudo(fuser, random.choice(
                ["sudo -l", "/usr/bin/find . -exec /bin/bash \\; -quit", "cat /etc/passwd"]), fip)
        with LOCK:
            cpu = 15 + random.random() * 25
            SYSTEM["cpu"] = round(cpu, 1)
            SYSTEM["ts"] = now()
            for s in SYSTEM.get("sessions", []):
                s["frozen"] = s["user"] in FROZEN_USERS
        STOP.wait(random.uniform(0.25, 0.9))


# --------------------------------------------------------------------------- #
# Vue JSON                                                                    #
# --------------------------------------------------------------------------- #
def build_state():
    with LOCK:
        ips = []
        for r in IPS.values():
            b = BLOCKS.get(r["ip"])
            ips.append({
                "ip": r["ip"], "mac": r["mac"], "first": r["first"], "last": r["last"],
                "person": SESSION_BY_IP.get(r["ip"]),
                "ssh": {"fail": r["ssh"]["fail"], "ok": r["ssh"]["ok"], "invalid": r["ssh"]["invalid"],
                        "users": sorted(r["ssh"]["users"].items(), key=lambda x: -x[1])[:12]},
                "http": {"req": r["http"]["req"], "last_status": r["http"]["last_status"],
                         "paths": sorted(r["http"]["paths"].items(), key=lambda x: -x[1])[:12]},
                "smb": r["smb"]["conn"], "snmp": r["snmp"]["hits"], "live": r["live"],
                "activity": r["ssh"]["fail"] + r["ssh"]["ok"] + r["http"]["req"] + r["smb"]["conn"] + r["snmp"]["hits"],
                "block": b["type"] if b else None, "block_until": b["until"] if b else None,
                "recent": [{"ts": e["ts"], "service": e["service"], "level": e["level"], "detail": e["detail"]}
                           for e in list(r["events"])[-14:]],
            })
        events = [dict(e) for e in list(EVENTS)[-140:]]
        sudo = [dict(e) for e in list(SUDO_EVENTS)[-40:]]
        blocks = [{"ip": ip, **b} for ip, b in BLOCKS.items()]
        system = dict(SYSTEM)
        if system.get("sessions"):
            system["sessions"] = [dict(s, frozen=s["user"] in FROZEN_USERS) for s in system["sessions"]]
        stats = {
            "ips": len(IPS),
            "ssh_fail": sum(r["ssh"]["fail"] for r in IPS.values()),
            "ssh_ok": sum(r["ssh"]["ok"] for r in IPS.values()),
            "http": sum(r["http"]["req"] for r in IPS.values()),
            "blocks": len(BLOCKS), "demo": STATE["demo"], "now": now(),
            "uptime": now() - STATE["started"], "recording": bool(_REC["dir"]),
        }
    return {"stats": stats, "ips": ips, "events": events, "sudo": sudo,
            "blocks": blocks, "system": system}


# --------------------------------------------------------------------------- #
# Serveur HTTP + auth par cookie                                             #
# --------------------------------------------------------------------------- #
TOKEN = ""
PAGE = ""
LOGIN = ""


class Handler(BaseHTTPRequestHandler):
    timeout = 20                      # ferme les connexions lentes (anti-slowloris)

    def log_message(self, *a):
        pass

    def _cookie_ok(self):
        c = self.headers.get("Cookie", "")
        try:
            jar = http.cookies.SimpleCookie(c)
            if "arene" in jar and compare_digest(jar["arene"].value, TOKEN):
                return True
        except Exception:
            pass
        return False

    def _authed(self):
        return self._cookie_ok()      # cookie de session uniquement (jamais de jeton dans l'URL)

    def _send(self, code, body, ctype="application/json", extra=None):
        data = body.encode("utf-8") if isinstance(body, str) else body
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        for k, v in (extra or []):
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)

    def _redirect(self, to, extra=None):
        self.send_response(302)
        self.send_header("Location", to)
        for k, v in (extra or []):
            self.send_header(k, v)
        self.end_headers()

    def do_GET(self):
        path = urlparse(self.path).path
        if path == "/login":
            self._send(200, LOGIN, "text/html; charset=utf-8"); return
        if path == "/logout":
            self._redirect("/login", [("Set-Cookie", "arene=; Path=/; Max-Age=0")]); return
        if not self._authed():
            if path == "/" or path.startswith("/api"):
                if path.startswith("/api"):
                    self._send(403, json.dumps({"error": "auth"})); return
                self._redirect("/login"); return
            self._send(403, "auth", "text/plain"); return
        if path == "/" or path == "/index.html":
            self._send(200, PAGE, "text/html; charset=utf-8")
        elif path == "/api/state":
            self._send(200, json.dumps(build_state()))
        elif path == "/api/export":
            self._export(parse_qs(urlparse(self.path).query))
        else:
            self._send(404, "not found", "text/plain")

    def _export(self, qs):
        what = qs.get("what", ["events"])[0]
        if what == "state":
            self._send(200, json.dumps(build_state(), ensure_ascii=False), "application/json",
                       [("Content-Disposition", "attachment; filename=arene-state.json")])
            return
        body = ""
        try:
            if _REC["fh"]:
                _REC["fh"].flush()
            if _REC["dir"]:
                fn = os.path.join(_REC["dir"], "arene-%s.jsonl" % time.strftime("%Y%m%d"))
                if os.path.exists(fn):
                    with open(fn, encoding="utf-8") as f:
                        body = f.read()
        except Exception:
            pass
        self._send(200, body or "(journal vide)\n", "text/plain; charset=utf-8",
                   [("Content-Disposition", "attachment; filename=arene-journal.jsonl")])

    def do_POST(self):
        path = urlparse(self.path).path
        try:
            n = int(self.headers.get("Content-Length", 0))
            if n > MAX_BODY:
                self._send(413, json.dumps({"error": "corps trop volumineux"})); return
            raw = self.rfile.read(n) if n else b""
        except Exception:
            self._send(400, json.dumps({"error": "corps"})); return
        if path == "/login":
            key = parse_qs(raw.decode("utf-8", "replace")).get("key", [""])[0]
            if compare_digest(key, TOKEN):
                self._redirect("/", [("Set-Cookie",
                    "arene=%s; Path=/; HttpOnly; SameSite=Strict" % TOKEN)])
            else:
                self._redirect("/login?e=1")
            return
        if not self._authed():
            self._send(403, json.dumps({"error": "auth"})); return
        try:
            payload = json.loads(raw or "{}")
        except Exception:
            self._send(400, json.dumps({"error": "json"})); return
        try:
            if path == "/api/action":
                apply_block(payload["ip"], payload["type"], payload.get("minutes", 0))
            elif path == "/api/release":
                clear_block(payload["ip"])
            elif path == "/api/freeze":
                freeze_session(payload["ip"])
            elif path == "/api/wake":
                wake_user(payload["user"])
            else:
                self._send(404, json.dumps({"error": "route"})); return
        except Exception as e:
            self._send(400, json.dumps({"error": str(e)})); return
        self._send(200, json.dumps({"ok": True}))


# --------------------------------------------------------------------------- #
# Pages                                                                       #
# --------------------------------------------------------------------------- #
LOGIN_TMPL = r'''<!doctype html><html lang="fr"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>ARENE — Connexion</title>
<style>
:root{--bg:#0a0e14;--panel:#111823;--line:#26374d;--txt:#d6e2f0;--muted:#7d8ea3;--accent:#3ddc97}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--txt);
 font:14px ui-monospace,Menlo,Consolas,monospace;display:grid;place-items:center;height:100vh}
.box{background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:30px 34px;width:340px}
h1{font-size:17px;letter-spacing:2px;margin:0 0 4px}h1 b{color:var(--accent)}
p{color:var(--muted);font-size:12px;margin:0 0 18px}
input{width:100%;padding:10px;border-radius:8px;border:1px solid var(--line);background:#0d141d;color:var(--txt);font:inherit}
button{width:100%;margin-top:12px;padding:10px;border-radius:8px;border:0;background:var(--accent);color:#08110b;font-weight:700;cursor:pointer}
.err{color:#ff5d6c;font-size:12px;margin-top:10px;min-height:16px}
</style></head><body>
<form class="box" method="post" action="/login">
  <h1>ARENE <b>//</b> EDGE01</h1>
  <p>Tour de contrôle — accès réservé formateur.</p>
  <input type="password" name="key" placeholder="jeton d'accès" autofocus autocomplete="off">
  <button type="submit">Entrer</button>
  <div class="err" id="err"></div>
</form>
<script>if(location.search.indexOf("e=1")>=0)document.getElementById("err").textContent="Jeton invalide.";</script>
</body></html>'''

PAGE_TMPL = r'''<!doctype html><html lang="fr"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>ARENE — Surveillance EDGE01</title>
<style>
:root{--bg:#0a0e14;--panel:#111823;--panel2:#0d141d;--line:#1e2a3a;--line2:#26374d;
 --txt:#d6e2f0;--muted:#7d8ea3;--accent:#3ddc97;--cyan:#38bdf8;
 --fail:#ff5d6c;--warn:#ffb454;--ok:#3ddc97;--chip:#17222f}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--txt);font:13.5px/1.45 ui-monospace,Menlo,Consolas,monospace}
header{display:flex;align-items:center;gap:12px;padding:11px 16px;background:linear-gradient(180deg,#0d141d,#0a0e14);border-bottom:1px solid var(--line2);flex-wrap:wrap}
header h1{font-size:15px;margin:0;letter-spacing:2px}header h1 b{color:var(--accent)}
.dot{width:9px;height:9px;border-radius:50%;background:var(--accent);box-shadow:0 0 8px var(--accent);animation:pulse 1.6s infinite}
@keyframes pulse{50%{opacity:.35}}
.spacer{flex:1}
.badge{font-size:11px;padding:2px 8px;border-radius:20px;border:1px solid var(--line2);color:var(--muted)}
.badge.demo{color:#0a0e14;background:var(--warn);border-color:var(--warn);font-weight:700}
.badge.rec{color:#0a0e14;background:var(--fail);border-color:var(--fail);font-weight:700}
a.btn,button{font:inherit;color:var(--txt);background:var(--panel2);border:1px solid var(--line2);border-radius:7px;padding:5px 9px;cursor:pointer;text-decoration:none}
button:hover,a.btn:hover{border-color:var(--cyan)}
.sys{display:flex;gap:10px;padding:12px 16px;flex-wrap:wrap;border-bottom:1px solid var(--line)}
.metric{background:var(--panel);border:1px solid var(--line);border-radius:9px;padding:8px 12px;min-width:96px}
.metric .k{font-size:10px;color:var(--muted);text-transform:uppercase;letter-spacing:1px}
.metric .v{font-size:19px;font-weight:700;margin-top:2px}
.bar{height:5px;border-radius:3px;background:#0d141d;margin-top:5px;overflow:hidden}
.bar>i{display:block;height:100%;background:var(--accent)}
.bar>i.hot{background:var(--fail)}.bar>i.warm{background:var(--warn)}
.svcs{display:flex;gap:6px;align-items:center;flex-wrap:wrap}
.svc-b{font-size:11px;padding:3px 8px;border-radius:6px;background:var(--chip);border:1px solid var(--line2)}
.svc-b.up{color:var(--ok);border-color:#265a3f}.svc-b.down{color:var(--fail);border-color:#5a2630}
.wrap{display:grid;grid-template-columns:1.7fr 1fr;gap:14px;padding:14px 16px}
@media(max-width:1050px){.wrap{grid-template-columns:1fr}}
.pane{background:var(--panel);border:1px solid var(--line);border-radius:10px;overflow:hidden;margin-bottom:14px}
.pane h2{font-size:12px;margin:0;padding:9px 13px;color:var(--muted);text-transform:uppercase;letter-spacing:1px;border-bottom:1px solid var(--line)}
.controls{display:flex;gap:8px;align-items:center;flex-wrap:wrap;padding:9px 13px;border-bottom:1px solid var(--line)}
input,select{font:inherit;color:var(--txt);background:var(--panel2);border:1px solid var(--line2);border-radius:7px;padding:5px 8px}
table{width:100%;border-collapse:collapse;font-size:12.5px}
th,td{padding:6px 9px;text-align:left;border-bottom:1px solid var(--line)}
th{color:var(--muted);font-weight:600;font-size:10.5px;text-transform:uppercase;cursor:pointer;position:sticky;top:0;background:var(--panel)}
tr.iprow{cursor:pointer}tr.iprow:hover{background:#0e1620}
tr.blk td{background:rgba(255,93,108,.07)}
.mono{font-family:inherit}
.person{color:var(--warn);font-weight:700}
.svc{display:inline-block;font-size:10px;padding:1px 5px;border-radius:4px;margin:1px;background:var(--chip);border:1px solid var(--line2);color:var(--muted)}
.svc.live{color:#0a0e14;background:var(--accent);border-color:var(--accent);font-weight:700}
.num{font-weight:700}.num.f{color:var(--fail)}.num.o{color:var(--ok)}
.state{font-size:10px;padding:1px 7px;border-radius:20px;font-weight:700}
.state.ban{background:#3a1219;color:var(--fail)}.state.freeze{background:#0e2233;color:var(--cyan)}.state.slow{background:#3a2a12;color:var(--warn)}
.det td{background:var(--panel2);padding:11px 15px}
.kv{display:flex;flex-wrap:wrap;gap:6px;margin:3px 0 9px}
.tag{font-size:11px;padding:2px 8px;border-radius:6px;background:var(--chip);border:1px solid var(--line2)}.tag b{color:var(--cyan)}
.sub{color:var(--muted);font-size:10.5px;text-transform:uppercase;letter-spacing:1px;margin:8px 0 4px}
.act{display:flex;gap:6px;flex-wrap:wrap;margin:5px 0}
.b-slow{background:#3a2a12;border-color:#5a4626;color:var(--warn)}
.b-freeze{background:#0e2233;border-color:#265a5a;color:var(--cyan)}
.b-ban{background:#2a0f14;border-color:#5a2630;color:var(--fail)}
.b-rel{background:#0f2a1c;border-color:#265a3f;color:var(--ok)}
.feed{max-height:44vh;overflow:auto}
.ev{display:flex;gap:8px;padding:4px 12px;border-bottom:1px solid #131c27;font-size:11.5px;align-items:baseline}
.ev .t{color:var(--muted);width:40px;flex:none}.ev .s{width:56px;flex:none;font-size:10px;color:var(--muted)}
.ev .i{width:104px;flex:none;color:var(--cyan)}
.ev.fail .d{color:var(--fail)}.ev.warn .d{color:var(--warn)}.ev.ok .d{color:var(--ok)}
.sess{display:flex;align-items:center;gap:8px;padding:7px 12px;border-bottom:1px solid var(--line)}
.sess .u{font-weight:700;color:var(--warn)}.sess.frz .u{color:var(--cyan)}
.sess .m{color:var(--muted);font-size:11px}.sess .r{margin-left:auto;display:flex;gap:6px}
.empty{padding:18px;text-align:center;color:var(--muted)}
</style></head>
<body>
<header>
  <span class="dot"></span><h1>ARENE <b>//</b> EDGE01</h1>
  <span class="badge demo" id="demoBadge" style="display:none">DEMO</span>
  <span class="badge rec" id="recBadge" style="display:none">● REC</span>
  <span class="spacer"></span>
  <span class="badge" id="uptime">—</span>
  <a class="btn" href="/api/export?what=events">↓ journal</a>
  <a class="btn" href="/api/export?what=state">↓ état</a>
  <a class="btn" href="/logout">quitter</a>
</header>

<div class="sys" id="sys"></div>

<div class="wrap">
  <div>
    <div class="pane">
      <h2>Sources — cibler par personne / IP / MAC</h2>
      <div class="controls">
        <input id="search" placeholder="filtrer IP / MAC / personne…" style="min-width:200px">
        <span class="spacer" style="flex:1"></span>
        <label style="color:var(--muted);font-size:11px"><input type="checkbox" id="auto" checked style="width:auto"> auto</label>
        <button id="refresh">rafraichir</button>
      </div>
      <div style="max-height:60vh;overflow:auto">
        <table><thead><tr>
          <th data-k="ip">IP</th><th data-k="person">Personne</th><th data-k="mac">MAC</th>
          <th>Services</th><th data-k="ssh.fail">SSH ✗/✓</th><th data-k="http.req">HTTP</th>
          <th data-k="last">Vu</th><th>État</th>
        </tr></thead><tbody id="rows"></tbody></table>
      </div>
    </div>
  </div>
  <div>
    <div class="pane"><h2>Sessions actives</h2><div id="sessions"><div class="empty">aucune session</div></div></div>
    <div class="pane"><h2>Élévation — sudo / su (jeudi)</h2><div class="feed" id="sudo"></div></div>
    <div class="pane"><h2>IP sous contrôle</h2><div id="blocks"><div class="empty">aucune</div></div></div>
    <div class="pane"><h2>Flux live</h2><div class="feed" id="feed"></div></div>
  </div>
</div>

<script>
const CFG=__CFG__;
let sortKey="activity",sortDir=-1,filter="";
const expanded=new Set();
let last={stats:{now:Date.now()/1000},ips:[],events:[],sudo:[],blocks:[],system:{}};

function el(t,c,x){const e=document.createElement(t);if(c)e.className=c;if(x!=null)e.textContent=x;return e;}
function ago(ts,nw){let s=Math.max(0,Math.floor(nw-ts));if(s<60)return s+"s";if(s<3600)return Math.floor(s/60)+"m";return Math.floor(s/3600)+"h";}
function hhmm(ts){const d=new Date(ts*1000);return String(d.getHours()).padStart(2,"0")+":"+String(d.getMinutes()).padStart(2,"0");}
function get(o,p){return p.split(".").reduce((a,k)=>a==null?a:a[k],o);}
function human(n){if(!n)return"0";const u=["","K","M","G","T"];let i=0;while(n>=1024&&i<4){n/=1024;i++;}return n.toFixed(i?1:0)+u[i];}

document.getElementById("search").oninput=e=>{filter=e.target.value.toLowerCase().trim();render();};
document.getElementById("refresh").onclick=fetchState;
document.querySelectorAll("th[data-k]").forEach(th=>th.onclick=()=>{const k=th.dataset.k;if(sortKey===k)sortDir*=-1;else{sortKey=k;sortDir=-1;}render();});

async function api(path,body){const r=await fetch(path,{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(body)});return r.json();}
async function act(ip,type,minutes){const r=await api("/api/action",{ip,type,minutes:minutes||0});if(r.error)alert("Refusé: "+r.error);fetchState();}
async function release(ip){await api("/api/release",{ip});fetchState();}
async function freeze(ip){const r=await api("/api/freeze",{ip});if(r.error)alert("Refusé: "+r.error);fetchState();}
async function wake(u){await api("/api/wake",{user:u});fetchState();}

async function fetchState(){
  try{const r=await fetch("/api/state",{cache:"no-store"});if(!r.ok)throw 0;last=await r.json();render();}
  catch(e){document.querySelector(".dot").style.background="var(--fail)";}
}

function render(){
  const st=last.stats,nw=st.now,sys=last.system||{};
  document.getElementById("demoBadge").style.display=st.demo?"inline":"none";
  document.getElementById("recBadge").style.display=st.recording?"inline":"none";
  const up=Math.floor(st.uptime);document.getElementById("uptime").textContent="uptime "+(up<3600?Math.floor(up/60)+"m":Math.floor(up/3600)+"h");

  // ---- système ----
  const S=document.getElementById("sys");S.innerHTML="";
  function metric(k,v,pct,cls){const m=el("div","metric");m.append(el("div","k",k),el("div","v",v));
    if(pct!=null){const b=el("div","bar");const i=el("i",pct>85?"hot":pct>60?"warm":"");i.style.width=Math.min(100,pct)+"%";b.appendChild(i);m.appendChild(b);}return m;}
  if(sys.cpu!=null)S.appendChild(metric("CPU",sys.cpu+"%",sys.cpu));
  if(sys.mem_total){const used=100*(1-sys.mem_avail/sys.mem_total);S.appendChild(metric("MÉM",human(( sys.mem_total-sys.mem_avail)*1024),used));}
  if(sys.disk_total){const used=100*(1-sys.disk_free/sys.disk_total);S.appendChild(metric("DISQUE",human(sys.disk_free)+" libre",used));}
  if(sys.load)S.appendChild(metric("CHARGE",sys.load.join(" ")));
  if(sys.uptime)S.appendChild(metric("UPTIME",(sys.uptime<3600?Math.floor(sys.uptime/60)+"m":Math.floor(sys.uptime/3600)+"h")));
  if(sys.services){const box=el("div","metric");box.append(el("div","k","SERVICES"));const row=el("div","svcs");
    Object.entries(sys.services).forEach(([n,stt])=>{const up=stt==="active";row.appendChild(el("span","svc-b "+(up?"up":"down"),n));});box.appendChild(row);S.appendChild(box);}

  // ---- table ----
  let rows=last.ips.slice();
  if(filter)rows=rows.filter(r=>(r.ip+" "+(r.mac||"")+" "+(r.person||"")).toLowerCase().includes(filter));
  rows.sort((a,b)=>{let x=get(a,sortKey),y=get(b,sortKey);if(typeof x==="string"){x=x||"";y=y||"";return sortDir*x.localeCompare(y);}return sortDir*((x||0)-(y||0));});
  const tb=document.getElementById("rows");tb.innerHTML="";
  if(!rows.length){const tr=el("tr"),td=el("td");td.colSpan=8;td.className="empty";td.textContent="aucune source";tr.appendChild(td);tb.appendChild(tr);}
  rows.forEach(r=>{
    const tr=el("tr","iprow"+(r.block?" blk":""));tr.onclick=()=>{expanded.has(r.ip)?expanded.delete(r.ip):expanded.add(r.ip);render();};
    tr.appendChild(el("td","mono",r.ip));
    tr.appendChild(el("td","person",r.person||"—"));
    tr.appendChild(el("td","mono",r.mac||"—"));
    const svc=el("td");["SSH","HTTP","SMB","SNMP"].forEach(s=>{const seen=(s==="SSH"&&r.ssh.fail+r.ssh.ok>0)||(s==="HTTP"&&r.http.req>0)||(s==="SMB"&&r.smb>0)||(s==="SNMP"&&r.snmp>0)||r.live.includes(s);if(seen)svc.appendChild(el("span","svc"+(r.live.includes(s)?" live":""),s));});tr.appendChild(svc);
    const ssh=el("td");ssh.append(el("span","num f",r.ssh.fail),el("span",null," / "),el("span","num o",r.ssh.ok));tr.appendChild(ssh);
    tr.appendChild(el("td","num",r.http.req||"—"));
    tr.appendChild(el("td",null,ago(r.last,nw)));
    const stt=el("td");if(r.block){const s=el("span","state "+r.block,r.block+(r.block_until?" "+Math.max(0,Math.floor(r.block_until-nw))+"s":""));stt.appendChild(s);}else stt.textContent="—";tr.appendChild(stt);
    tb.appendChild(tr);
    if(expanded.has(r.ip)){
      const dtr=el("tr","det"),dtd=el("td");dtd.colSpan=8;
      dtd.appendChild(el("div","sub","Actions ciblées"));
      const bar=el("div","act");
      const mk=(cls,txt,fn)=>{const b=el("button",cls,txt);b.onclick=(e)=>{e.stopPropagation();fn();};return b;};
      bar.appendChild(mk("b-slow","ralentir",()=>act(r.ip,"slow",0)));
      bar.appendChild(mk("b-freeze","geler",()=>act(r.ip,"freeze",0)));
      [5,15,60].forEach(m=>bar.appendChild(mk("b-ban","bannir "+m+"m",()=>act(r.ip,"ban",m))));
      if(r.block)bar.appendChild(mk("b-rel","relâcher",()=>release(r.ip)));
      if(r.person)bar.appendChild(mk("b-freeze","geler session "+r.person,()=>freeze(r.ip)));
      dtd.appendChild(bar);
      dtd.appendChild(el("div","sub","Utilisateurs SSH testés"));
      const kv=el("div","kv");if(r.ssh.users.length)r.ssh.users.forEach(([u,c])=>{const t=el("span","tag");t.append(document.createTextNode(u+" "));t.appendChild(el("b",null,"×"+c));kv.appendChild(t);});else kv.appendChild(el("span","tag","aucun"));dtd.appendChild(kv);
      dtd.appendChild(el("div","sub","Chemins HTTP"));
      const kv2=el("div","kv");if(r.http.paths.length)r.http.paths.forEach(([p,c])=>{const t=el("span","tag");t.append(document.createTextNode(p+" "));t.appendChild(el("b",null,"×"+c));kv2.appendChild(t);});else kv2.appendChild(el("span","tag","aucun"));dtd.appendChild(kv2);
      dtd.appendChild(el("div","sub","Événements récents"));
      r.recent.slice().reverse().forEach(e=>{const row=el("div","ev "+e.level);row.append(el("span","t",hhmm(e.ts)),el("span","s",e.service),el("span","d",e.detail));dtd.appendChild(row);});
      dtr.appendChild(dtd);tb.appendChild(dtr);
    }
  });

  // ---- sessions ----
  const sd=document.getElementById("sessions");sd.innerHTML="";
  const sess=(sys.sessions||[]);
  if(!sess.length)sd.appendChild(el("div","empty","aucune session"));
  sess.forEach(s=>{const row=el("div","sess"+(s.frozen?" frz":""));
    row.append(el("span","u",s.user),el("span","m",(s.ip||s.tty)+" · "+s.since));
    const r=el("span","r");
    if(s.frozen)r.appendChild((()=>{const b=el("button","b-rel","réveiller");b.onclick=()=>wake(s.user);return b;})());
    else if(s.ip)r.appendChild((()=>{const b=el("button","b-freeze","geler");b.onclick=()=>freeze(s.ip);return b;})());
    row.appendChild(r);sd.appendChild(row);});

  // ---- sudo / privesc ----
  const ud=document.getElementById("sudo");ud.innerHTML="";
  if(!last.sudo.length)ud.appendChild(el("div","empty","aucune commande sudo"));
  last.sudo.slice().reverse().forEach(e=>{const row=el("div","ev "+(e.privesc?"fail":"warn"));
    row.append(el("span","t",hhmm(e.ts)),el("span","i",e.user||"?"),el("span","d",(e.privesc?"⚠ ":"")+"sudo "+e.command));ud.appendChild(row);});

  // ---- blocks ----
  const bd=document.getElementById("blocks");bd.innerHTML="";
  if(!last.blocks.length)bd.appendChild(el("div","empty","aucune"));
  last.blocks.forEach(b=>{const row=el("div","sess");
    row.append(el("span","mono",b.ip),el("span","state "+b.type,b.type+(b.until?" "+Math.max(0,Math.floor(b.until-nw))+"s":"")));
    const r=el("span","r");const ub=el("button","b-rel","relâcher");ub.onclick=()=>release(b.ip);r.appendChild(ub);row.appendChild(r);bd.appendChild(row);});

  // ---- feed ----
  const fd=document.getElementById("feed");fd.innerHTML="";
  last.events.slice().reverse().forEach(e=>{const row=el("div","ev "+e.level);
    row.append(el("span","t",hhmm(e.ts)),el("span","s",e.service),el("span","i",e.ip),el("span","d",e.detail));fd.appendChild(row);});
}

setInterval(()=>{if(document.getElementById("auto").checked)fetchState();},2000);
fetchState();
</script></body></html>'''


# --------------------------------------------------------------------------- #
def discover_self_ips():
    ips = set()
    for line in run(["ip", "-o", "-4", "addr"]).splitlines():
        m = re.search(r"inet " + _IP, line)
        if m:
            ips.add(m.group(1))
    try:
        ips.add(socket.gethostbyname(socket.gethostname()))
    except Exception:
        pass
    ips.add("127.0.0.1")
    return ips


def main():
    global TOKEN, PAGE, LOGIN
    ap = argparse.ArgumentParser(description="ARENE - console de surveillance EDGE01")
    ap.add_argument("--host", default=None)
    ap.add_argument("--port", type=int, default=8899)
    ap.add_argument("--key", default=os.environ.get("ARENE_KEY", ""))
    ap.add_argument("--allow", default="", help="IP formateur a ne jamais bannir")
    ap.add_argument("--record", default=None, help="dossier du journal (defaut: ./arene_records ou /root/arene_records)")
    ap.add_argument("--no-record", action="store_true")
    ap.add_argument("--demo", action="store_true")
    args = ap.parse_args()

    STATE["demo"] = args.demo
    TOKEN = args.key or secrets.token_urlsafe(16)
    if args.key and len(args.key) < 12:
        log("ATTENTION : jeton court (<12 car.). Préfère un jeton long, ou omets --key (généré fort).")
    PAGE = PAGE_TMPL.replace("__CFG__", json.dumps({"demo": args.demo}))
    LOGIN = LOGIN_TMPL
    host = args.host or "127.0.0.1"    # loopback par défaut : invisible des élèves ; accès par tunnel SSH
    if args.allow:
        SAFE_IPS.add(args.allow)
    if not args.no_record:
        _REC["dir"] = args.record or (os.path.join(os.getcwd(), "arene_records")
                                      if args.demo else "/root/arene_records")
        STATE["record"] = _REC["dir"]

    if not args.demo:
        SELF_IPS.update(discover_self_ips())
        threading.Thread(target=stream_cmd, args=(["journalctl", "_COMM=sshd", "-n", "800", "-f", "-o", "cat", "--no-pager"], parse_ssh_line, "ssh"), daemon=True).start()
        threading.Thread(target=stream_cmd, args=(["journalctl", "_COMM=sudo", "_COMM=su", "_COMM=pkexec", "-n", "200", "-f", "-o", "cat", "--no-pager"], parse_sudo_line, "sudo"), daemon=True).start()
        threading.Thread(target=stream_cmd, args=(["tail", "-n", "400", "-F", NGINX_ACCESS], parse_nginx_line, "nginx"), daemon=True).start()
        threading.Thread(target=snapshot_loop, daemon=True).start()
        threading.Thread(target=system_loop, daemon=True).start()
    else:
        threading.Thread(target=demo_loop, daemon=True).start()
    threading.Thread(target=ban_expiry_loop, daemon=True).start()

    httpd = ThreadingHTTPServer((host, args.port), Handler)
    shown = host if host != "0.0.0.0" else (sorted(SELF_IPS - {"127.0.0.1"}) or ["<IP-EDGE01>"])[0]
    print("=" * 72)
    print(" ARENE — console de surveillance %s" % ("[DEMO]" if args.demo else "[LIVE]"))
    print(" Login : http://%s:%d/login" % (shown, args.port))
    print(" Jeton : %s" % TOKEN)
    if _REC["dir"]:
        print(" Journal : %s" % _REC["dir"])
    print(" (Ctrl-C : arret propre, leve bans/gels, ferme le journal)")
    print("=" * 72)
    if args.demo:
        try:
            import webbrowser
            threading.Timer(1.0, lambda: webbrowser.open("http://127.0.0.1:%d/login" % args.port)).start()
        except Exception:
            pass
    def _term(_signum, _frame):
        raise KeyboardInterrupt()
    for _s in ("SIGTERM", "SIGINT"):
        try:
            signal.signal(getattr(signal, _s), _term)
        except Exception:
            pass
    atexit.register(cleanup)
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        cleanup()
        print("\n[arene] arret — regles iptables + gels leves, journal ferme.")


if __name__ == "__main__":
    main()

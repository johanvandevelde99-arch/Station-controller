#!/usr/bin/env python3
"""
Stationcontroller controls via/with Hamlib, KMTronic relays, WSJT-X/JTDX

A native, standalone antenna/relay controller. Talks to
the KMTronic web-relay board directly over HTTP from Python, so there is no
browser, no CORS/mixed-content/login restriction to work around.

Requires only the Python standard library (tkinter + urllib), so it runs
with a plain `python stationcontroller.py`, and can be frozen into a
single .exe with PyInstaller:

    pip install pyinstaller
    pyinstaller --onefile --windowed --name "StationController" stationcontroller.py

The .exe will be in the dist/ folder. --windowed hides the console window.

CAT output: the frequency read from rigctld is also sent as
Kenwood-style 'FA00014200000;' (8N1) to up to TWO PC COM ports at a settable
interval. Both ports share the same baud rate, format and interval. Ports,
baud, interval and on/off live in the 'Output' menu. This part needs
pyserial (pip install pyserial); everything else is standard library.

Hamlib tab: the 'Hamlib' menu opens a built-in rigctld launcher (formerly the
separate hamlib_gui.py). It can download the latest Hamlib for Windows, list
the supported radios, set COM port / baud / CI-V / PTT, and start/stop
rigctld. Starting it points this program's CAT settings at it automatically,
and it can start by itself when the program launches.

Server / client: run it as a SERVER at the station (it alone controls the relay
board, CAT and output ports) and as a CLIENT on a remote PC over the internet.
Users and passwords (min. 10 characters), TLS with a pinned certificate, roles,
a single controlling client at a time, and a transmit interlock that blocks all
relay/direction changes while the rig is transmitting. See 'Remote operation'
below and the Remote menu.

WSJT-X / JTDX relay: the server can listen for the UDP stream of WSJT-X or JTDX
(default 127.0.0.1:2237, set the same address in the program's Reporting tab),
optionally copy it to up to 5 other targets (unicast or multicast), and pass it on to every client,
which re-emits it as local UDP. Optionally (own password, operator/admin only) the
client's program can answer back: Reply / Halt Tx / Free text are passed to the
server PC's WSJT-X/JTDX.

73 ON4IQ
"""

APP_VERSION = '3.0'  # bump this with each change; shown on the compass and sent to clients at login

import argparse
import base64
import glob
import hashlib
import hmac
import json
import math
import os
import queue
import re
import shutil
import secrets
import socket
import ssl
import struct
import subprocess
import sys
import threading
import time
import zipfile
import tkinter as tk
from tkinter import ttk, messagebox, colorchooser, simpledialog, filedialog
import urllib.request
import urllib.error
import xml.etree.ElementTree as ET

try:  # only needed for the amplifier COM-port output
    import serial
    from serial.tools import list_ports
except ImportError:
    serial = None
    list_ports = None

AMP_BAUDS = [1200, 2400, 4800, 9600, 19200, 38400, 57600, 115200]
AMP_INTERVALS = [100, 250, 500, 1000, 2000, 5000]  # ms presets; 'Custom...' allows any value

APP_TITLE = "Stationcontroller"

# ── Config location (next to the exe/script, so settings travel with it) ──
if getattr(sys, 'frozen', False):
    APP_DIR = os.path.dirname(sys.executable)
else:
    APP_DIR = os.path.dirname(os.path.abspath(__file__))
CFG_PATH = os.path.join(APP_DIR, '9ca_cfg.json')
FORCE_MODE = None   # set by --mode on the command line
START_MIN = False   # set by --minimized

DIRS = ['N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW']
ANGLES = {'N': 0, 'NE': 45, 'E': 90, 'SE': 135, 'S': 180, 'SW': 225, 'W': 270, 'NW': 315}

DEFAULT_PATTERNS = {
    'N':  [1, 1, 1, 1],
    'NE': [0, 0, 0, 0],
    'E':  [1, 1, 0, 0],
    'SE': [0, 0, 1, 0],
    'S':  [1, 1, 1, 0],
    'SW': [0, 0, 0, 1],
    'W':  [1, 1, 0, 1],
    'NW': [0, 0, 1, 1],
}
DEFAULT_AUX_LABELS = ['BPF 1', 'BPF 2', 'AUX 3', 'AUX 4']

# Default color each direction's button/arrow/wedge use when it's the active
# direction. One shared blue by default; customisable per-direction in Settings.
DEFAULT_DIR_COLORS = {d: '#0055cc' for d in DIRS}
DEFAULT_AUX_COLORS = ['#006600', '#006600', '#006600', '#006600']  # relays 5-8, when ON
DEFAULT_OFF_COLOR = '#cc0000'  # ALL OFF button

DEFAULT_THEME = {
    'appBg': '#f0f0f0',          # window background
    'canvasBg': '#ffffff',       # compass background
    'ringColor': '#cccccc',      # compass outer ring
    'wedgeColor': '#dbe8fa',     # shaded triangular beam behind the arrow
    'matrixBg': '#f0f0f0',       # idle (unselected) matrix direction button background
    'matrixText': '#000000',    # idle matrix direction button text
    'auxBg': '#f0f0f0',          # idle (OFF) aux relay button background
    'auxText': '#000000',       # idle aux relay button text
    'freqBg': '#001a00',         # frequency LED background
    'freqText': '#33ff33',      # frequency LED text (when a reading is shown)
}

# Built-in array presets. Each defines which of the 8 compass points the
# array actually uses, how many of the 8 relays are spent on direction
# switching (the rest become aux relays), and a starting pattern per
# direction (editable afterward in Settings, same as always).
ARRAY_PRESETS = [
    {
        # Truth table supplied directly by the user (read off the YCCC
        # manual's Figure 43 / pi4cc.nl), since pi4cc.nl's robots.txt and
        # DX Engineering's bot protection both blocked fetching it here.
        'key': '9ca', 'label': '9 Circle Array  (8 dir · relays 1-4)',
        'dirs': ['N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW'],
        'switchRelays': 4,
        'patterns': {
            'N':  [1, 1, 1, 1],
            'NE': [0, 0, 0, 0],
            'E':  [1, 1, 0, 0],
            'SE': [0, 0, 1, 0],
            'S':  [1, 1, 1, 0],
            'SW': [0, 0, 0, 1],
            'W':  [1, 1, 0, 1],
            'NW': [0, 0, 1, 1],
        },
    },
    {
        # Verified against LowBandSystems' own "4SQTX/8" PCB documentation
        # (Control logic / Truth Table, pins 1-6; pin 7 n/c, pin 8 = common).
        # Despite the "4 square" name this unit gives 8 directions using 6
        # switching relays, matching what was asked for here.
        'key': 'lbs4sq8', 'label': 'LBS 4 Square /8  (8 dir · relays 1-6, verified)',
        'dirs': ['N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW'],
        'switchRelays': 6,
        'patterns': {
            'N':  [1, 0, 0, 1, 0, 0],
            'NE': [0, 0, 0, 0, 0, 0],
            'E':  [0, 0, 1, 1, 0, 1],
            'SE': [1, 1, 1, 1, 1, 1],
            'S':  [0, 1, 1, 0, 0, 1],
            'SW': [0, 0, 0, 0, 1, 1],
            'W':  [1, 1, 0, 0, 0, 1],
            'NW': [1, 1, 1, 1, 0, 0],
        },
    },
    {
        'key': '4sq', 'label': '4 Square  (4 dir · relays 1-2)',
        'dirs': ['N', 'E', 'S', 'W'],
        'switchRelays': 2,
        'patterns': {'N': [0, 0], 'E': [0, 1], 'S': [1, 0], 'W': [1, 1]},
    },
    {
        # NOTE: no manufacturer-published relay truth table for a K9AY
        # switch box was found, unlike the LBS 4SQ/8 table above. This uses
        # the standard convention for this class of receive switchbox —
        # exactly one dedicated relay energized per direction, the rest
        # off — rather than a binary code. If your actual K9AY controller
        # wires it differently, tell me the real pattern and I'll correct it.
        'key': 'k9ay', 'label': 'K9AY Loop  (4 dir · relays 1-4, one relay/dir)',
        'dirs': ['N', 'E', 'S', 'W'],
        'switchRelays': 4,
        'patterns': {'N': [1, 0, 0, 0], 'E': [0, 1, 0, 0], 'S': [0, 0, 1, 0], 'W': [0, 0, 0, 1]},
    },
    {
        # Same caveat as K9AY above: no published truth table found, so
        # this uses the same one-relay-per-wire convention typical of a
        # 4-wire BOG (Beverage on Ground) switch box.
        'key': 'bog', 'label': 'BOG  (4 dir · relays 1-4, one relay/dir)',
        'dirs': ['N', 'E', 'S', 'W'],
        'switchRelays': 4,
        'patterns': {'N': [1, 0, 0, 0], 'E': [0, 1, 0, 0], 'S': [0, 0, 1, 0], 'W': [0, 0, 0, 1]},
    },
]


def make_binary_patterns(dirs, switch_relays):
    """Sequential binary code per direction, used for custom arrays and as
    a fallback when resizing an existing array to a new relay count."""
    if switch_relays <= 0:
        # list[-0:] is list[0:] (the WHOLE list) in Python, not an empty
        # one, since -0 == 0 — so this case needs handling explicitly or
        # every direction gets a full-length pattern instead of none,
        # which then collides with the aux relays' own numbering.
        return {d: [] for d in dirs}
    return {d: [int(b) for b in format(i, f'0{switch_relays}b')][-switch_relays:]
            for i, d in enumerate(dirs)}


DEFAULT_CFG = {
    'beamWidth': 45,        # full width (degrees) of the shaded wedge behind the arrow
    'transport': 'udp',    # 'udp' (port 12345, no login) or 'http' (web interface)
    'host': '192.168.2.190',
    'port': 12345,         # UDP default; 80 is typical for HTTP
    'user': 'admin',
    'password': 'admin',
    'mode': 'ff',          # HTTP only: 'ff' = /FF0101 direct on/off, 'toggle' = /relays.cgi?relay=N
    'demo': True,
    'offset': 0,
    'dirPatterns': DEFAULT_PATTERNS,
    'auxLabels': DEFAULT_AUX_LABELS,
    'dirColors': DEFAULT_DIR_COLORS,
    'auxColors': DEFAULT_AUX_COLORS,
    'offColor': DEFAULT_OFF_COLOR,
    'theme': DEFAULT_THEME,
    'arrayPreset': '9ca',
    'arrayDirs': list(DIRS),
    'switchRelays': 4,
    'customArrays': [],  # user-defined arrays saved via Array → Define new array…
    'savedPatterns': {},  # {presetKey: {dir: [bits...]}} — each array remembers its own edits
    'savedOffsets': {},   # {presetKey: offset} — offset belongs to the array, not global
    'catEnabled': False,
    'catHost': '127.0.0.1',
    'catPort': 4532,       # rigctld's default TCP port
    'catPollMs': 2000,
    # Each entry: {'min': kHz, 'max': kHz, 'aux': aux-relay-index-or-None}.
    # The first range whose min/max contains the rig's current frequency
    # decides which aux relay (if any) is switched ON; all other aux relays
    # are switched OFF. Used for frequency-dependent BPF/array switching.
    'freqRanges': [],
    'ampEnabled': False,   # send Kenwood-style FA frequency to the amplifier's COM port
    'ampPort': '',         # output port 1 ('' = unused)
    'ampPort2': '',        # output port 2 ('' = unused); shares baud/format/interval with port 1
    'ampBaud': 9600,       # 8 data bits, no parity, 1 stop bit (fixed)
    'ampIntervalMs': 1000,
    'hamlib': {},          # settings of the built-in Hamlib/rigctld tab (see HamlibPanel)
    'appMode': 'standalone',       # 'standalone' | 'server' | 'client' (applies after a restart)
    'startMinimized': False,
    'remote': {                    # see RemoteDialog; users themselves live in users.json
        'sBind': '0.0.0.0', 'sPort': 8765,
        'cHost': '', 'cPort': 8765, 'cUser': '', 'cPassword': '', 'cRemember': True, 'cFingerprint': '',
    },
    'txInterlock': True,           # block relay/direction changes while the rig is transmitting
    'txInterlockFailClosed': False,  # also block when the PTT state cannot be read
    'wsjt': {                      # WSJT-X / JTDX UDP stream (see WsjtListener)
        'enabled': False,          # server: listen + forward to clients; client: re-emit locally
        'listen': '127.0.0.1', 'port': 2237,     # server: where WSJT-X/JTDX sends to (multicast allowed)
        'relays': [],              # server: also copy the stream to up to 5 targets [{'host':..., 'port':...}]
        'outHost': '127.0.0.1', 'outPort': 2237,  # client: re-emit the received stream here
        'ctlEnabled': False,       # server: accept control from clients; client: send replies back
        'ctlHash': {},             # server: salted scrypt hash of the control password
        'ctlPassword': '',         # client: control password (only kept if 'remember' is on)
    },
    'pst': {                       # PstRotator UDP protocol as input: azimuth -> closest direction
        'enabled': False, 'listen': '127.0.0.1', 'port': 12000, 'reply': True,
    },
}


def load_cfg():
    cfg = json.loads(json.dumps(DEFAULT_CFG))  # deep copy
    try:
        with open(CFG_PATH, 'r', encoding='utf-8') as f:
            saved = json.load(f)
        cfg.update(saved)
        if 'dirPatterns' not in saved:
            cfg['dirPatterns'] = DEFAULT_PATTERNS
        if 'dirColors' not in saved:
            cfg['dirColors'] = dict(DEFAULT_DIR_COLORS)
        else:
            # fill in any direction missing a saved color (e.g. older config file)
            for d in DIRS:
                cfg['dirColors'].setdefault(d, DEFAULT_DIR_COLORS[d])
        if 'auxColors' not in saved or len(cfg.get('auxColors', [])) < 4:
            cfg['auxColors'] = list(DEFAULT_AUX_COLORS)
        if 'offColor' not in saved:
            cfg['offColor'] = DEFAULT_OFF_COLOR
        if 'theme' not in saved:
            cfg['theme'] = dict(DEFAULT_THEME)
        else:
            for k, v in DEFAULT_THEME.items():
                cfg['theme'].setdefault(k, v)
        if 'auxLabels' not in saved:
            cfg['auxLabels'] = DEFAULT_AUX_LABELS
        cfg.setdefault('arrayPreset', '9ca')
        cfg.setdefault('arrayDirs', list(DIRS))
        cfg.setdefault('switchRelays', 4)
        cfg.setdefault('customArrays', [])
        cfg.setdefault('savedPatterns', {})
        cfg.setdefault('savedOffsets', {})
        cfg.setdefault('beamWidth', 45)
        cfg.setdefault('catEnabled', False)
        cfg.setdefault('catHost', '127.0.0.1')
        cfg.setdefault('catPort', 4532)
        cfg.setdefault('catPollMs', 2000)
        cfg.setdefault('freqRanges', [])
        cfg.setdefault('ampEnabled', False)
        cfg.setdefault('ampPort', '')
        cfg.setdefault('ampPort2', '')
        cfg.setdefault('ampBaud', 9600)
        cfg.setdefault('ampIntervalMs', 1000)
        cfg.setdefault('hamlib', {})
        cfg.setdefault('txInterlock', True)
        cfg.setdefault('txInterlockFailClosed', False)
        cfg.setdefault('appMode', 'standalone')
        cfg.setdefault('startMinimized', False)
        cfg['remote'] = {**DEFAULT_CFG['remote'], **(cfg.get('remote') or {})}
        cfg['wsjt'] = {**DEFAULT_CFG['wsjt'], **(cfg.get('wsjt') or {})}
        cfg['pst'] = {**DEFAULT_CFG['pst'], **(cfg.get('pst') or {})}
        w = cfg['wsjt']  # settings of v2.1-2.4 had one copy target: carry it over
        old_host = str(w.pop('relayHost', '') or '').strip()
        old_port = w.pop('relayPort', 2238)
        if old_host and not w.get('relays'):
            w['relays'] = [{'host': old_host, 'port': old_port}]
    except (OSError, ValueError):
        pass
    return cfg


def save_cfg(cfg):
    try:
        with open(CFG_PATH, 'w', encoding='utf-8') as f:
            json.dump(cfg, f, indent=2)
    except OSError:
        pass


# ──────────────────────────────────────────────────────────────────────────
# KMTronic comms (runs in a background thread, never blocks the UI)
# Supports two transports:
#   - UDP (the original KMTronic UDP boards): send the ASCII command
#     ("FF0101" etc) as raw bytes in one UDP packet to the board's UDP port
#     (12345 by default). No login. Status is read by sending "FF0000" and
#     parsing the ASCII reply the board sends back.
#   - HTTP (KMTronic WEB boards): GET requests to the board's web server,
#     optionally with Basic auth.
# ──────────────────────────────────────────────────────────────────────────
class KMTronic:
    def __init__(self, cfg_getter, log):
        self.cfg_getter = cfg_getter
        self.log = log

    # ---------- HTTP ----------
    def _base_url(self):
        cfg = self.cfg_getter()
        port = cfg.get('port') or 80
        p = '' if port in (80, '', None) else f':{port}'
        return f"http://{cfg['host']}{p}"

    def _auth_header(self):
        cfg = self.cfg_getter()
        user = cfg.get('user', '')
        pw = cfg.get('password', '')
        token = base64.b64encode(f'{user}:{pw}'.encode()).decode()
        return f'Basic {token}'

    def _http_get(self, path):
        cfg = self.cfg_getter()
        url = f"{self._base_url()}/{path}"
        if cfg.get('demo'):
            self.log(f"[DEMO] GET {url}")
            time.sleep(0.05)
            return True, None
        req = urllib.request.Request(url, headers={'Authorization': self._auth_header()})
        try:
            with urllib.request.urlopen(req, timeout=4) as r:
                return True, r.read()
        except urllib.error.HTTPError as e:
            # Some KMTronic firmware answers /FF0101 with 404 even though the
            # relay switches fine, so any HTTP response counts as reaching
            # the board.
            self.log(f"GET {url} -> HTTP {e.code} (command still applied)")
            return True, e.read()
        except Exception as e:
            self.log(f"ERROR reaching board: {e}")
            return False, None

    # ---------- UDP ----------
    def _udp_send(self, command, expect_reply=False, reply_size=64, timeout=1.5):
        """Send an ASCII command (e.g. 'FF0101') as raw bytes in one UDP
        packet. Optionally wait briefly for a reply (used for status reads).
        Returns (ok, reply_bytes_or_None)."""
        cfg = self.cfg_getter()
        host = cfg['host']
        port = int(cfg.get('port') or 12345)
        if cfg.get('demo'):
            self.log(f"[DEMO] UDP -> {host}:{port}  {command}")
            time.sleep(0.05)
            return True, None
        try:
            sock_ = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            sock_.settimeout(timeout)
            sock_.sendto(command.encode('ascii'), (host, port))
            reply = None
            if expect_reply:
                try:
                    reply, _ = sock_.recvfrom(reply_size)
                except socket.timeout:
                    self.log(f"UDP {command} sent, no reply within {timeout}s "
                              f"(command may still have been applied)")
            sock_.close()
            self.log(f"UDP -> {host}:{port}  {command}")
            return True, reply
        except Exception as e:
            self.log(f"ERROR sending UDP to {host}:{port}: {e}")
            return False, None

    # ---------- transport-agnostic ----------
    @staticmethod
    def relay_command(relay_num, state):
        return f"FF{relay_num:02X}{'01' if state else '00'}"

    def send_relay(self, relay_num, state, relay_state):
        cfg = self.cfg_getter()
        transport = cfg.get('transport', 'udp')
        if transport == 'udp':
            ok, _ = self._udp_send(self.relay_command(relay_num, state))
        else:
            if cfg.get('mode') == 'toggle':
                if relay_state[relay_num - 1] == state:
                    return True
                ok, _ = self._http_get(f"relays.cgi?relay={relay_num}")
            else:
                ok, _ = self._http_get(self.relay_command(relay_num, state))
        if ok:
            relay_state[relay_num - 1] = state
        return ok

    def all_off(self, relay_state):
        cfg = self.cfg_getter()
        if cfg.get('transport', 'udp') == 'udp':
            ok, _ = self._udp_send('FFE000')
            if ok:
                for i in range(8):
                    relay_state[i] = False
            return ok
        for i in range(1, 9):
            if not self.send_relay(i, False, relay_state):
                return False
        return True

    def read_status(self):
        """Returns a list of 8 booleans, or None if unreadable/demo."""
        cfg = self.cfg_getter()
        if cfg.get('demo'):
            return None
        if cfg.get('transport', 'udp') == 'udp':
            ok, reply = self._udp_send('FF0000', expect_reply=True)
            if not ok or not reply:
                return None
            # Boards reply with an ASCII string of 8 '0'/'1' digits (relay 1..8),
            # sometimes with extra framing bytes around it; pull out the digits.
            text = ''.join(ch for ch in reply.decode('ascii', errors='ignore') if ch in '01')
            if len(text) < 8:
                return None
            return [c == '1' for c in text[:8]]
        ok, body = self._http_get('status.xml')
        if not ok or not body:
            return None
        try:
            root = ET.fromstring(body)
            st = []
            for i in range(8):
                node = root.find(f'relay{i}')
                st.append(bool(node is not None and node.text and node.text.strip() == '1'))
            return st
        except ET.ParseError:
            return None


# ──────────────────────────────────────────────────────────────────────────
# CAT (Hamlib rigctld) — reads the rig's frequency over rigctld's plain-text
# TCP protocol. This does NOT talk to the radio directly: Hamlib's rigctld
# must already be running (it's part of any standard Hamlib install) and
# connected to the actual rig; this just queries rigctld itself.
# ──────────────────────────────────────────────────────────────────────────
class CAT:
    def __init__(self, cfg_getter, log):
        self.cfg_getter = cfg_getter
        self.log = log

    def get_status(self):
        """(freq_khz_or_None, ptt_or_None): see get_status_full()."""
        return self.get_status_full()[:2]

    @staticmethod
    def _reply_complete(data):
        """True once the replies to 'f', 't' and 'm' have all arrived. 'm' answers with two
        lines (mode, passband), or one 'RPRT -n' line if the rig cannot report its mode."""
        done = data.decode('ascii', errors='ignore').split('\n')[:-1]  # last item = unfinished line
        return len(done) >= 3 and (done[2].startswith('RPRT') or len(done) >= 4)

    def get_status_full(self):
        """Ask rigctld for frequency ('f'), PTT ('t') and mode ('m') in one connection.
        Returns (freq_khz_or_None, ptt_or_None, mode_or_None). ptt is True while transmitting,
        False on receive, None if the rig/rigctld can't report it; mode is e.g. 'USB', 'LSB',
        'CW', 'PKTUSB' (None if not reported). All None means rigctld could not be reached."""
        cfg = self.cfg_getter()
        try:
            with socket.create_connection((cfg['catHost'], cfg['catPort']), timeout=1.5) as s:
                s.sendall(b'f\nt\nm\n')
                s.settimeout(1.5)
                data = b''
                while not self._reply_complete(data):
                    try:
                        chunk = s.recv(128)
                    except socket.timeout:
                        break  # slow rig: use what has arrived
                    if not chunk:
                        break
                    data += chunk
        except Exception as e:
            self.log(f'CAT error: {e}')
            return None, None, None
        lines = data.decode('ascii', errors='ignore').split('\n')
        freq = ptt = mode = None
        try:
            freq = float(lines[0].strip()) / 1000.0
        except (ValueError, IndexError):
            self.log(f'CAT: unreadable frequency reply {lines[:1]!r}')
        try:
            # rigctld: 0 = RX, 1 = TX, 2 = TX via mic, 3 = TX via data. 'RPRT -n' = not supported.
            ptt = int(lines[1].strip()) in (1, 2, 3)
        except (ValueError, IndexError):
            ptt = None
        if len(lines) > 2:
            m = lines[2].strip().upper()
            if m and not m.startswith('RPRT') and m.replace('-', '').isalnum():
                mode = m
        return freq, ptt, mode

    def get_freq_khz(self):
        """Returns the rig's current frequency in kHz, or None on failure."""
        return self.get_status()[0]

    @staticmethod
    def find_range(freq_khz, ranges):
        """First range (in list order) whose min/max contains freq_khz."""
        for r in ranges:
            try:
                if r['min'] <= freq_khz <= r['max']:
                    return r
            except (KeyError, TypeError):
                continue
        return None


# ──────────────────────────────────────────────────────────────────────────
# Hamlib tab — a rigctld launcher (integrated from hamlib_gui.py). It does not
# talk to the radio itself: it downloads/locates Hamlib, runs rigctld with the
# chosen radio and port, and tells the main app where to find it for CAT.
# Its settings live under the 'hamlib' key of the main config file.
# ──────────────────────────────────────────────────────────────────────────
IS_WIN = os.name == 'nt'
EXE = '.exe' if IS_WIN else ''
NO_WINDOW = subprocess.CREATE_NO_WINDOW if IS_WIN else 0
HAMLIB_DIR = os.path.join(APP_DIR, 'hamlib')
HAMLIB_LEGACY_CFG = os.path.join(APP_DIR, 'hamlib_gui.json')  # imported once if present
HAMLIB_API_LATEST = 'https://api.github.com/repos/Hamlib/Hamlib/releases/latest'
HL_BAUDS = ['1200', '2400', '4800', '9600', '19200', '38400', '57600', '115200']
HL_PTT_TYPES = ['(default)', 'RIG', 'RTS', 'DTR', 'CM108', 'GPIO', 'NONE']


def hl_find_bin_dir(root):
    """Return the folder that contains rigctld(.exe) somewhere under root."""
    if not root or not os.path.isdir(root):
        return None
    for dirpath, _dirs, files in os.walk(root):
        if 'rigctld' + EXE in files:
            return dirpath
    return None


def hl_autodetect_bin_dir(saved=None):
    candidates = [saved, HAMLIB_DIR]
    candidates += glob.glob(r'C:\Program Files\hamlib*') + glob.glob(r'C:\Program Files (x86)\hamlib*')
    candidates += glob.glob(r'C:\hamlib*')
    for c in candidates:
        found = hl_find_bin_dir(c)
        if found:
            return found
    which = shutil.which('rigctld')
    return os.path.dirname(which) if which else None


def hl_list_serial_ports():
    ports = []
    if IS_WIN:
        try:
            import winreg
            key = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r'HARDWARE\DEVICEMAP\SERIALCOMM')
            i = 0
            while True:
                try:
                    ports.append(winreg.EnumValue(key, i)[1])
                    i += 1
                except OSError:
                    break
        except OSError:
            pass
    else:
        ports = glob.glob('/dev/ttyUSB*') + glob.glob('/dev/ttyACM*')
    if list_ports:  # pyserial, when installed, also sees adapters the registry list misses
        try:
            ports += [p.device for p in list_ports.comports()]
        except Exception:
            pass
    return sorted(set(ports), key=lambda p: (len(p), p))


def hl_parse_rig_list(text):
    """Parse `rigctl -l` output into [(id, mfg, model)]."""
    rigs = []
    for line in text.splitlines():
        parts = re.split(r'\s{2,}', line.strip())
        if len(parts) >= 3 and parts[0].isdigit():
            rigs.append((int(parts[0]), parts[1], parts[2]))
    return rigs


# ── PstRotator UDP protocol as input ──
# Loggers and rotator programs control a PstRotator by sending it UDP messages on port 12000, e.g.
#   <PST><AZIMUTH>123</AZIMUTH></PST>      go to azimuth 123 degrees
#   <PST>AZ?</PST>                         ask for the current azimuth (answer 'AZ:123.0' on port+1)
# Here such an azimuth selects the closest direction of the active array. Other commands are ignored.
PST_PORT_DEFAULT = 12000
PST_AZ_RE = re.compile(rb'<AZIMUTH>\s*(-?\d{1,4}(?:[.,]\d{1,6})?)\s*</AZIMUTH>', re.I)
PST_QUERY_RE = re.compile(rb'<PST>\s*AZ\?\s*</PST>', re.I)


def pst_parse(data):
    """('az', degrees 0..360) for an azimuth command, ('query', None) for AZ?, else None."""
    if len(data) > 512:
        return None
    m = PST_AZ_RE.search(data)
    if m:
        return 'az', float(m.group(1).replace(b',', b'.')) % 360
    if PST_QUERY_RE.search(data):
        return 'query', None
    return None


class PstListener:
    """Receives the PstRotator UDP protocol and hands each command to the UI thread."""
    def __init__(self, app):
        self.app = app
        self.sock = None
        self.thread = None
        self.error = ''
        self.listening = ''
        self.count = 0

    def start(self):
        self.stop()
        self.error = ''
        pc = self.app.cfg.get('pst', {})
        if not pc.get('enabled'):
            return
        host = (pc.get('listen') or '127.0.0.1').strip()
        try:
            port = int(pc.get('port', PST_PORT_DEFAULT))
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            try:
                s.bind((host, port))  # no SO_REUSEADDR: a clash with a running PstRotator must be visible
                s.settimeout(0.5)
            except Exception:
                s.close()
                raise
        except (OSError, ValueError) as e:
            self.error = str(e)
            print(f'[pst] cannot listen: {e}')
            return
        self.sock = s
        self.listening = f'{host}:{port}'
        self.thread = threading.Thread(target=self._loop, args=(s,), daemon=True)
        self.thread.start()

    def stop(self):
        s, self.sock = self.sock, None
        if s:
            try:
                s.close()
            except OSError:
                pass
        t = self.thread
        if t and t is not threading.current_thread():
            t.join(2.0)
        self.thread = None
        self.listening = ''

    def _loop(self, s):
        while self.sock is s:
            try:
                data, addr = s.recvfrom(1024)
            except socket.timeout:
                continue
            except ConnectionResetError:
                continue
            except OSError:
                break
            cmd = pst_parse(data)
            if cmd is None or self.app.ui_q.qsize() > 200:
                continue
            self.count += 1
            self.app.ui_q.put(lambda k=cmd[0], v=cmd[1], a=addr: self.app._pst_command(k, v, a))


# ── Scrolling container used by every window ──
class ScrollFrame(ttk.Frame):
    """A frame with scroll bars (shown only when the content does not fit). Build the window's
    widgets in .inner. The window opens at the content's natural size, capped to the screen,
    and can be resized freely: what does not fit is reached with the bars or the mouse wheel
    (Shift+wheel = sideways).
      stretch: the content grows with the window (otherwise it keeps its natural size)
      center : keep a smaller content centred horizontally"""
    _wheel_ready = False

    def __init__(self, parent, stretch=False, center=False, **kw):
        super().__init__(parent, **kw)
        self.stretch, self.center = stretch, center
        self.vbar_visible = self.hbar_visible = False
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)
        bg = ttk.Style(self).lookup('TFrame', 'background')
        self.canvas = tk.Canvas(self, highlightthickness=0, borderwidth=0,
                                yscrollincrement=20, xscrollincrement=20, **({'bg': bg} if bg else {}))
        self.vbar = ttk.Scrollbar(self, orient='vertical', command=self.canvas.yview)
        self.hbar = ttk.Scrollbar(self, orient='horizontal', command=self.canvas.xview)
        self.canvas.configure(yscrollcommand=self.vbar.set, xscrollcommand=self.hbar.set)
        self.canvas.grid(row=0, column=0, sticky='nsew')
        self.inner = ttk.Frame(self.canvas)
        self._win = self.canvas.create_window(0, 0, window=self.inner, anchor='nw')
        self.inner.bind('<Configure>', self._relayout)
        self.canvas.bind('<Configure>', self._relayout)
        ScrollFrame._install_wheel(self)

    def _relayout(self, _e=None):
        c = self.canvas
        iw, ih = self.inner.winfo_reqwidth(), self.inner.winfo_reqheight()
        # the window asks for the content's size, but never more than the screen offers
        tw = max(1, min(iw, self.winfo_screenwidth() - 120))
        th = max(1, min(ih, self.winfo_screenheight() - 200))
        if (int(c.cget('width')), int(c.cget('height'))) != (tw, th):
            c.configure(width=tw, height=th)
        cw, ch = c.winfo_width(), c.winfo_height()
        W, H = self.winfo_width(), self.winfo_height()
        if self.stretch:
            w, h, x = max(iw, cw), max(ih, ch), 0
        else:
            w, h = iw, ih
            x = max(0, (cw - iw) // 2) if self.center else 0
        c.itemconfigure(self._win, width=w, height=h)
        c.coords(self._win, x, 0)
        c.configure(scrollregion=(0, 0, max(w + x, cw), max(h, ch)))
        if W > 1 and H > 1:  # bars: only when the content is bigger than the window
            vb, hb = self.vbar.winfo_reqwidth(), self.hbar.winfo_reqheight()
            need_v, need_h = ih > H, iw > W
            if need_v and not need_h and iw > W - vb:
                need_h = True
            if need_h and not need_v and ih > H - hb:
                need_v = True
            if need_v != self.vbar_visible:
                self.vbar_visible = need_v
                (self.vbar.grid(row=0, column=1, sticky='ns') if need_v else self.vbar.grid_remove())
            if need_h != self.hbar_visible:
                self.hbar_visible = need_h
                (self.hbar.grid(row=1, column=0, sticky='ew') if need_h else self.hbar.grid_remove())

    # one global mouse-wheel handler: finds the ScrollFrame under the pointer
    @staticmethod
    def _wheel_target(widget):
        if not isinstance(widget, tk.Misc):
            return None
        try:
            if getattr(widget, '_no_wheel_scroll', False) or \
                    widget.winfo_class() in ('Text', 'Listbox', 'Treeview', 'TCombobox', 'Spinbox', 'TSpinbox'):
                return None  # these scroll (or use the wheel) themselves
        except tk.TclError:
            return None
        w = widget
        while w is not None:
            if isinstance(w, ScrollFrame):
                return w
            w = getattr(w, 'master', None)
        return None

    @staticmethod
    def _on_wheel(event):
        sf = ScrollFrame._wheel_target(event.widget)
        if sf is None:
            return
        if getattr(event, 'num', None) in (4, 5):
            step = -1 if event.num == 4 else 1
        else:
            step = -1 if event.delta > 0 else 1
        if event.state & 0x1:  # Shift: sideways
            if sf.hbar_visible:
                sf.canvas.xview_scroll(step * 3, 'units')
        elif sf.vbar_visible:
            sf.canvas.yview_scroll(step * 3, 'units')

    @staticmethod
    def _install_wheel(widget):
        if not ScrollFrame._wheel_ready:
            ScrollFrame._wheel_ready = True
            for seq in ('<MouseWheel>', '<Button-4>', '<Button-5>'):
                widget.bind_all(seq, ScrollFrame._on_wheel, add='+')


class HamlibPanel(ttk.Frame):
    LOG_MAX_LINES = 2000  # -v makes rigctld chatty; keep the log box from growing forever

    def __init__(self, parent, app):
        super().__init__(parent)
        self.app = app
        self._loading = True            # don't write the config while the widgets are being set up
        self.rigs = []
        self.visible_rigs = []
        self.proc = None
        self.log_q = queue.Queue()      # log lines from any thread
        self.ui_q = queue.Queue()       # callables from worker threads, run on the UI thread

        # one-time import of the old stand-alone tool's settings
        if not self.hc and os.path.exists(HAMLIB_LEGACY_CFG):
            try:
                with open(HAMLIB_LEGACY_CFG, 'r', encoding='utf-8') as f:
                    self.app.cfg['hamlib'] = json.load(f)
                self.log('Imported settings from hamlib_gui.json')
            except (OSError, ValueError):
                pass

        self.bin_dir = hl_autodetect_bin_dir(self.hc.get('bin_dir'))
        self.model_id = self.hc.get('model')
        self._build_ui()
        self.refresh_ports()
        self._loading = False
        self.after(100, self._pump)

        if self.bin_dir:
            self.log(f'Using Hamlib in: {self.bin_dir}')
            self.load_radios()
        else:
            self.log("Hamlib not found. Click 'Download latest Hamlib' or 'Browse...'.")
        self.show_radio_info()
        self.update_buttons()
        if self.auto_var.get() and self.bin_dir and self.model_id and self.app.app_mode != 'client':
            self.after(1000, self.start)  # let the main window finish opening first

    # the main app replaces its cfg dict when Settings are applied, so never cache it
    @property
    def hc(self):
        return self.app.cfg.setdefault('hamlib', {})

    def save_config(self):
        if self._loading:
            return
        self.hc.update({
            'bin_dir': self.bin_dir or '',
            'model': self.model_id,
            'port': self.port_var.get(),
            'baud': self.baud_var.get(),
            'tcp': self.tcp_var.get(),
            'civ': self.civ_var.get(),
            'ptt': self.ptt_var.get(),
            'ptt_port': self.ptt_port_var.get(),
            'extra': self.extra_var.get(),
            'verbose': self.verbose_var.get(),
            'autostart': self.auto_var.get(),
            'use_for_cat': self.cat_var.get(),
        })
        save_cfg(self.app.cfg)

    # ---- UI
    def _build_ui(self):
        pad = {'padx': 6, 'pady': 3}
        c = self.hc

        top = ttk.LabelFrame(self, text='Hamlib installation')
        top.pack(fill='x', padx=8, pady=(8, 4))
        self.dir_label = ttk.Label(top, text=self.bin_dir or 'Not found', anchor='w')
        self.dir_label.pack(side='left', fill='x', expand=True, **pad)
        ttk.Button(top, text='Browse...', command=self.browse_dir).pack(side='right', **pad)
        self.dl_btn = ttk.Button(top, text='Download latest Hamlib', command=self.download_hamlib)
        self.dl_btn.pack(side='right', **pad)

        mid = ttk.Frame(self)
        mid.pack(fill='both', expand=True, padx=8, pady=4)

        left = ttk.LabelFrame(mid, text='Radio')
        left.pack(side='left', fill='both', expand=True)
        self.search_var = tk.StringVar()
        self.search_var.trace_add('write', lambda *_: self.fill_radio_list())
        row = ttk.Frame(left)
        row.pack(fill='x', **pad)
        ttk.Label(row, text='Search:').pack(side='left')
        ttk.Entry(row, textvariable=self.search_var).pack(side='left', fill='x', expand=True, padx=4)
        lf = ttk.Frame(left)
        lf.pack(fill='both', expand=True, **pad)
        self.radio_list = tk.Listbox(lf, exportselection=False, height=10)
        sb = ttk.Scrollbar(lf, orient='vertical', command=self.radio_list.yview)
        self.radio_list.config(yscrollcommand=sb.set)
        self.radio_list.pack(side='left', fill='both', expand=True)
        sb.pack(side='right', fill='y')
        self.radio_list.bind('<<ListboxSelect>>', self.on_radio_select)
        self.radio_info = ttk.Label(left, text='No radio selected')
        self.radio_info.pack(fill='x', **pad)

        right = ttk.LabelFrame(mid, text='Connection')
        right.pack(side='right', fill='y', padx=(8, 0))
        self.port_var = tk.StringVar(value=c.get('port', ''))
        self.baud_var = tk.StringVar(value=c.get('baud', '9600'))
        self.tcp_var = tk.StringVar(value=c.get('tcp', '4532'))
        self.civ_var = tk.StringVar(value=c.get('civ', ''))
        self.ptt_var = tk.StringVar(value=c.get('ptt', HL_PTT_TYPES[0]))
        self.ptt_port_var = tk.StringVar(value=c.get('ptt_port', ''))
        self.extra_var = tk.StringVar(value=c.get('extra', ''))
        self.verbose_var = tk.BooleanVar(value=c.get('verbose', True))
        self.auto_var = tk.BooleanVar(value=c.get('autostart', False))
        self.cat_var = tk.BooleanVar(value=c.get('use_for_cat', True))

        def field(r, label, widget):
            ttk.Label(right, text=label).grid(row=r, column=0, sticky='w', **pad)
            widget.grid(row=r, column=1, sticky='ew', **pad)

        prow = ttk.Frame(right)
        self.port_cb = ttk.Combobox(prow, textvariable=self.port_var, width=12)
        self.port_cb.pack(side='left', fill='x', expand=True)
        ttk.Button(prow, text='\u21bb', width=3, command=self.refresh_ports).pack(side='left', padx=(3, 0))
        field(0, 'COM port:', prow)
        field(1, 'Baud rate:', ttk.Combobox(right, textvariable=self.baud_var, values=HL_BAUDS, width=16))
        field(2, 'TCP port:', ttk.Entry(right, textvariable=self.tcp_var, width=18))
        field(3, 'CI-V address:', ttk.Entry(right, textvariable=self.civ_var, width=18))
        field(4, 'PTT type:', ttk.Combobox(right, textvariable=self.ptt_var, values=HL_PTT_TYPES,
                                          state='readonly', width=16))
        field(5, 'PTT port:', ttk.Entry(right, textvariable=self.ptt_port_var, width=18))
        field(6, 'Extra args:', ttk.Entry(right, textvariable=self.extra_var, width=18))
        ttk.Checkbutton(right, text='Verbose log (-v)', variable=self.verbose_var).grid(
            row=7, column=0, columnspan=2, sticky='w', **pad)
        ttk.Checkbutton(right, text='Use as CAT source for this program',
                        variable=self.cat_var).grid(row=8, column=0, columnspan=2, sticky='w', **pad)
        ttk.Checkbutton(right, text='Start rigctld when this program starts',
                        variable=self.auto_var).grid(row=9, column=0, columnspan=2, sticky='w', **pad)
        ttk.Label(right, text='CI-V: e.g. 94 for IC-7300\n(leave empty if unsure)',
                  foreground='#666').grid(row=10, column=0, columnspan=2, sticky='w', **pad)

        bar = ttk.Frame(self)
        bar.pack(fill='x', padx=8, pady=4)
        self.start_btn = ttk.Button(bar, text='\u25b6 Start rigctld', command=self.start)
        self.start_btn.pack(side='left', padx=4)
        self.stop_btn = ttk.Button(bar, text='\u25a0 Stop', command=self.stop)
        self.stop_btn.pack(side='left', padx=4)
        self.freq_btn = ttk.Button(bar, text='Read frequency', command=self.read_freq)
        self.freq_btn.pack(side='left', padx=4)
        self.status = ttk.Label(bar, text='Stopped', foreground='#a00')
        self.status.pack(side='right', padx=8)

        for v in (self.port_var, self.baud_var, self.tcp_var, self.civ_var, self.ptt_var,
                  self.ptt_port_var, self.extra_var, self.verbose_var, self.auto_var, self.cat_var):
            v.trace_add('write', lambda *_: self.save_config())

        lg = ttk.LabelFrame(self, text='Log')
        lg.pack(fill='both', expand=True, padx=8, pady=(0, 8))
        self.log_box = tk.Text(lg, height=9, state='disabled', wrap='word',
                               background='#111', foreground='#ddd', font=('Consolas', 9))
        lsb = ttk.Scrollbar(lg, orient='vertical', command=self.log_box.yview)
        self.log_box.config(yscrollcommand=lsb.set)
        self.log_box.pack(side='left', fill='both', expand=True)
        lsb.pack(side='right', fill='y')

    # ---- logging + cross-thread plumbing (workers never touch widgets directly)
    def log(self, msg):
        self.log_q.put(msg)

    def _pump(self):
        try:
            while True:
                msg = self.log_q.get_nowait()
                self.log_box.config(state='normal')
                self.log_box.insert('end', msg.rstrip('\n') + '\n')
                if int(self.log_box.index('end-1c').split('.')[0]) > self.LOG_MAX_LINES:
                    self.log_box.delete('1.0', f'{self.LOG_MAX_LINES // 4}.0')
                self.log_box.see('end')
                self.log_box.config(state='disabled')
        except queue.Empty:
            pass
        try:
            while True:
                self.ui_q.get_nowait()()
        except queue.Empty:
            pass
        if self.proc and self.proc.poll() is not None:  # rigctld died or was closed from outside
            self.log(f'rigctld exited with code {self.proc.returncode}')
            self.proc = None
            self.update_buttons()
        self.after(100, self._pump)

    # ---- Hamlib install
    def set_bin_dir(self, path):
        self.bin_dir = path
        self.dir_label.config(text=path or 'Not found')
        self.save_config()
        self.update_buttons()
        if path:
            self.load_radios()

    def browse_dir(self):
        d = filedialog.askdirectory(title='Select your Hamlib folder (contains bin\\rigctld.exe)')
        if not d:
            return
        found = hl_find_bin_dir(d)
        if not found:
            messagebox.showerror('Not found', 'rigctld' + EXE + ' was not found in that folder.')
            return
        self.set_bin_dir(found)
        self.log(f'Using Hamlib in: {found}')

    def download_hamlib(self):
        self.dl_btn.config(state='disabled')
        threading.Thread(target=self._download_worker, daemon=True).start()

    def _download_worker(self):
        try:
            self.log('Checking latest Hamlib release on GitHub...')
            req = urllib.request.Request(HAMLIB_API_LATEST, headers={'User-Agent': 'stationcontroller'})
            with urllib.request.urlopen(req, timeout=30) as r:
                rel = json.load(r)
            asset = next((a for a in rel.get('assets', [])
                          if re.match(r'hamlib-w64-.*\.zip$', a['name'])), None)
            if not asset:
                raise RuntimeError('No hamlib-w64 zip found in the latest release.')
            self.log(f"Downloading {asset['name']} ({asset['size'] // 1024} KB)...")
            os.makedirs(HAMLIB_DIR, exist_ok=True)
            zpath = os.path.join(HAMLIB_DIR, asset['name'])
            req = urllib.request.Request(asset['browser_download_url'],
                                         headers={'User-Agent': 'stationcontroller'})
            with urllib.request.urlopen(req, timeout=120) as r, open(zpath, 'wb') as f:
                shutil.copyfileobj(r, f)
            self.log('Extracting...')
            with zipfile.ZipFile(zpath) as z:
                z.extractall(HAMLIB_DIR)
            os.remove(zpath)
            found = hl_find_bin_dir(HAMLIB_DIR)
            if not found:
                raise RuntimeError('Downloaded, but rigctld.exe not found in archive.')
            self.log(f"Installed Hamlib {rel.get('tag_name', '')} to {found}")
            self.ui_q.put(lambda: self.set_bin_dir(found))
        except Exception as e:  # noqa: BLE001
            self.log(f'Download failed: {e}')
        finally:
            self.ui_q.put(lambda: self.dl_btn.config(state='normal'))

    # ---- radio list
    def load_radios(self):
        bin_dir = self.bin_dir

        def worker():
            try:
                out = subprocess.run([os.path.join(bin_dir, 'rigctl' + EXE), '-l'],
                                     capture_output=True, text=True, timeout=60,
                                     cwd=bin_dir, creationflags=NO_WINDOW).stdout
                rigs = hl_parse_rig_list(out)
                self.rigs = rigs
                self.log(f'Loaded {len(rigs)} supported radios.')
                self.ui_q.put(self.fill_radio_list)
            except Exception as e:  # noqa: BLE001
                self.log(f'Could not list radios: {e}')
        threading.Thread(target=worker, daemon=True).start()

    def fill_radio_list(self):
        q = self.search_var.get().strip().lower()
        self.radio_list.delete(0, 'end')
        self.visible_rigs = []
        for rid, mfg, model in self.rigs:
            label = f'{mfg} {model}  [{rid}]'
            if q and q not in label.lower():
                continue
            self.visible_rigs.append(rid)
            self.radio_list.insert('end', label)
            if rid == self.model_id:
                idx = self.radio_list.size() - 1
                self.radio_list.selection_set(idx)
                self.radio_list.see(idx)
        self.show_radio_info()

    def on_radio_select(self, _e=None):
        sel = self.radio_list.curselection()
        if sel:
            self.model_id = self.visible_rigs[sel[0]]
            for rid, mfg, model in self.rigs:
                if rid == self.model_id:
                    self.hc['model_name'] = f'{mfg} {model}'
            self.show_radio_info()
            self.save_config()

    def show_radio_info(self):
        for rid, mfg, model in self.rigs:
            if rid == self.model_id:
                self.radio_info.config(text=f'Selected: {mfg} {model} (model {rid})')
                return
        if self.model_id and self.hc.get('model_name'):
            self.radio_info.config(text=f"Selected: {self.hc['model_name']} (model {self.model_id})")
        else:
            self.radio_info.config(text='No radio selected')

    def refresh_ports(self):
        ports = hl_list_serial_ports()
        self.port_cb['values'] = ports
        if not self.port_var.get() and ports:
            self.port_var.set(ports[0])

    # ---- run / stop
    def running(self):
        return self.proc is not None and self.proc.poll() is None

    def update_buttons(self):
        run = self.running()
        have = bool(self.bin_dir)
        self.start_btn.config(state='normal' if have and not run else 'disabled')
        self.stop_btn.config(state='normal' if run else 'disabled')
        self.freq_btn.config(state='normal' if run else 'disabled')
        self.status.config(text='Running' if run else 'Stopped',
                           foreground='#080' if run else '#a00')

    def tcp_port(self):
        return int(self.tcp_var.get().strip() or 4532)

    def build_command(self):
        cmd = [os.path.join(self.bin_dir, 'rigctld' + EXE), '-m', str(self.model_id)]
        if self.port_var.get().strip():
            cmd += ['-r', self.port_var.get().strip()]
        if self.baud_var.get().strip():
            cmd += ['-s', self.baud_var.get().strip()]
        cmd += ['-t', str(self.tcp_port())]
        if self.civ_var.get().strip():
            cmd += ['-c', self.civ_var.get().strip()]
        if self.ptt_var.get() != HL_PTT_TYPES[0]:
            cmd += ['-P', self.ptt_var.get()]
        if self.ptt_port_var.get().strip():
            cmd += ['-p', self.ptt_port_var.get().strip()]
        if self.verbose_var.get():
            cmd += ['-v']
        if self.extra_var.get().strip():
            cmd += self.extra_var.get().split()
        return cmd

    def start(self):
        if self.running() or not self.bin_dir:
            return
        if not self.model_id:
            messagebox.showwarning('Select a radio', 'Please choose your radio from the list first.')
            return
        try:
            tcp = self.tcp_port()
        except ValueError:
            messagebox.showerror('Invalid', 'TCP port must be a number.')
            return
        cmd = self.build_command()
        self.save_config()
        self.log('Starting: ' + ' '.join(cmd))
        try:
            self.proc = subprocess.Popen(cmd, cwd=self.bin_dir, stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT, text=True,
                                         creationflags=NO_WINDOW)
        except OSError as e:
            messagebox.showerror('Failed to start', str(e))
            return
        threading.Thread(target=self._reader, args=(self.proc,), daemon=True).start()
        self.update_buttons()
        if self.cat_var.get():
            self.app.hamlib_started(tcp)

    def _reader(self, proc):
        for line in proc.stdout:
            self.log(line)

    def stop(self):
        if self.running():
            self.proc.terminate()
            try:
                self.proc.wait(timeout=3)
            except subprocess.TimeoutExpired:
                self.proc.kill()
            self.log('rigctld stopped.')
        self.proc = None
        self.update_buttons()

    def shutdown(self):
        """Called when the main window closes: don't leave rigctld running behind it."""
        self.save_config()
        self.stop()

    def read_freq(self):
        try:
            port = self.tcp_port()
        except ValueError:
            return

        def worker():
            try:
                with socket.create_connection(('127.0.0.1', port), timeout=4) as s:
                    s.sendall(b'f\n')
                    data = s.recv(256).decode(errors='replace').strip()
                self.log(f'Frequency reply: {data}')
            except OSError as e:
                self.log(f'Could not read frequency: {e}')
        threading.Thread(target=worker, daemon=True).start()


# ──────────────────────────────────────────────────────────────────────────
# Remote operation (server / client)
#
#   SERVER  the PC at the station. It alone talks to the relay board, rigctld
#           and the output COM ports. It listens (TLS) for clients, checks the
#           user name + password, and passes on their commands and pushes the
#           state (frequency, PTT, relays, direction) back to them.
#   CLIENT  the same program on a remote PC. It has no hardware access: it
#           shows what the server reports and sends commands to it.
#
# Security model
#   * Everything is TLS-encrypted. The server has a self-signed certificate;
#     the client pins its SHA-256 fingerprint on first use (like SSH) and
#     refuses to talk to a server whose certificate later changes.
#   * Users live in users.json next to the settings file: salted scrypt
#     hashes only, never passwords. Passwords must be at least MIN_PW_LEN
#     characters.
#   * Failed logins slow down and then lock out the source address.
#   * Roles: viewer (display only), operator (can switch), admin (can switch
#     and take control from another operator).
#   * Only one client controls at a time; the others see the state but are
#     refused until the controller has been idle CONTROL_IDLE_S seconds.
#   * The transmit interlock is enforced by the server's core (see
#     App._tx_guard), so no client can bypass it.
#   * rigctld and the relay board are never exposed: only the server's own
#     TLS port is. For extra safety run it through a VPN/tunnel as well.
# Messages are JSON lines over the TLS connection.
# ──────────────────────────────────────────────────────────────────────────
REMOTE_PORT_DEFAULT = 8765
MIN_PW_LEN = 10
MAX_PW_LEN = 128
ROLES = ('viewer', 'operator', 'admin')
MAX_LINE = 65536
MAX_CLIENTS = 8
CONTROL_IDLE_S = 30          # a controlling client keeps control this long after its last command
LOCKOUT_FAILS = 5            # failed logins from one address ...
LOCKOUT_WINDOW_S = 600       # ... within this many seconds ...
LOCKOUT_S = 900              # ... lock that address out for this long
HEARTBEAT_S = 5              # both ends send something at least this often
LINK_TIMEOUT_S = 20          # no data for this long -> the link is considered dead
# The part of the server's configuration a client needs to draw the same array.
CFG_VIEW_KEYS = ('arrayPreset', 'arrayDirs', 'switchRelays', 'dirPatterns', 'dirColors',
                 'auxLabels', 'auxColors', 'offset', 'beamWidth', 'catEnabled')


def side_file(name):
    """users.json, the certificate, the server log ... live next to the settings file."""
    return os.path.join(os.path.dirname(os.path.abspath(CFG_PATH)), name)


def fmt_fingerprint(hex_digest):
    h = hex_digest.replace(':', '').upper()
    return ':'.join(h[i:i + 2] for i in range(0, len(h), 2))


def cert_fingerprint(cert_path):
    """SHA-256 fingerprint of a PEM certificate file (hex, no colons) or None."""
    try:
        with open(cert_path, 'r', encoding='ascii') as f:
            der = ssl.PEM_cert_to_DER_cert(f.read())
        return hashlib.sha256(der).hexdigest().upper()
    except (OSError, ValueError):
        return None


def generate_certificate(cert_path, key_path):
    """Create a self-signed certificate (ECDSA P-256, valid 10 years). Needs the
    'cryptography' package, or failing that the openssl command."""
    names = ['localhost']
    try:
        host = socket.gethostname()
        if host and host not in names:
            names.append(host)
    except OSError:
        pass
    try:
        import datetime
        import ipaddress
        from cryptography import x509
        from cryptography.hazmat.primitives import hashes, serialization
        from cryptography.hazmat.primitives.asymmetric import ec
        from cryptography.x509.oid import NameOID
        key = ec.generate_private_key(ec.SECP256R1())
        name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, 'Station Controller')])
        now = datetime.datetime.now(datetime.timezone.utc)
        san = [x509.DNSName(n) for n in names] + [x509.IPAddress(ipaddress.ip_address('127.0.0.1'))]
        cert = (x509.CertificateBuilder().subject_name(name).issuer_name(name)
                .public_key(key.public_key()).serial_number(x509.random_serial_number())
                .not_valid_before(now - datetime.timedelta(days=1))
                .not_valid_after(now + datetime.timedelta(days=3650))
                .add_extension(x509.SubjectAlternativeName(san), critical=False)
                .sign(key, hashes.SHA256()))
        with open(key_path, 'wb') as f:
            f.write(key.private_bytes(serialization.Encoding.PEM,
                                      serialization.PrivateFormat.TraditionalOpenSSL,
                                      serialization.NoEncryption()))
        with open(cert_path, 'wb') as f:
            f.write(cert.public_bytes(serialization.Encoding.PEM))
    except ImportError:
        exe = shutil.which('openssl')
        if not exe:
            raise RuntimeError("Cannot create a certificate: install the 'cryptography' package "
                               "(pip install cryptography) or put openssl on the PATH.")
        san = ','.join('DNS:' + n for n in names) + ',IP:127.0.0.1'
        r = subprocess.run([exe, 'req', '-x509', '-newkey', 'ec', '-pkeyopt', 'ec_paramgen_curve:prime256v1',
                            '-nodes', '-days', '3650', '-subj', '/CN=Station Controller',
                            '-addext', 'subjectAltName=' + san, '-keyout', key_path, '-out', cert_path],
                           capture_output=True, text=True, creationflags=NO_WINDOW)
        if r.returncode != 0:
            raise RuntimeError('openssl failed: ' + (r.stderr or r.stdout).strip()[:200])
    try:
        os.chmod(key_path, 0o600)  # no effect on Windows, which uses folder permissions
    except OSError:
        pass


class UserStore:
    """Allowed users: name -> {role, salted scrypt hash}. Stored in users.json."""
    NAME_RE = re.compile(r'^[a-z0-9_.-]{1,32}$')
    SCRYPT = dict(n=2 ** 14, r=8, p=1)

    def __init__(self, path=None):
        self.path = path or side_file('users.json')
        self.lock = threading.Lock()
        self.users = {}
        self.load()
        # verifying an unknown user costs the same time as a known one, so the
        # response time doesn't reveal which user names exist
        self._dummy = self._make_hash('dummy-password-for-timing')

    # ---- persistence
    def load(self):
        try:
            with open(self.path, 'r', encoding='utf-8') as f:
                self.users = dict(json.load(f).get('users', {}))
        except (OSError, ValueError, AttributeError):
            self.users = {}

    def _save(self):
        tmp = self.path + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump({'version': 1, 'users': self.users}, f, indent=2)
        os.replace(tmp, self.path)
        try:
            os.chmod(self.path, 0o600)
        except OSError:
            pass

    # ---- hashing
    def _make_hash(self, pw):
        salt = secrets.token_bytes(16)
        rec = {'algo': 'scrypt', **self.SCRYPT, 'salt': salt.hex()}
        rec['hash'] = self._derive(pw, rec).hex()
        return rec

    @staticmethod
    def _derive(pw, rec):
        salt = bytes.fromhex(rec['salt'])
        if rec.get('algo') == 'scrypt':
            return hashlib.scrypt(pw.encode('utf-8'), salt=salt, n=rec['n'], r=rec['r'], p=rec['p'],
                                  dklen=32, maxmem=64 * 1024 * 1024)
        return hashlib.pbkdf2_hmac('sha256', pw.encode('utf-8'), salt, int(rec.get('iter', 600000)), 32)

    # ---- rules
    @classmethod
    def validate_name(cls, name):
        if not cls.NAME_RE.match(name or ''):
            return 'User name: 1-32 characters, lower-case letters, digits, . _ - only.'
        return None

    @staticmethod
    def validate_password(pw, name=''):
        """Returns an error text, or None if the password is acceptable."""
        if len(pw) < MIN_PW_LEN:
            return f'Password must be at least {MIN_PW_LEN} characters (it has {len(pw)}).'
        if len(pw) > MAX_PW_LEN:
            return f'Password must be at most {MAX_PW_LEN} characters.'
        if name and pw.lower() == name.lower():
            return 'Password must not be the same as the user name.'
        if len(set(pw)) < 4:
            return 'Password is too repetitive: use at least 4 different characters.'
        return None

    # ---- operations (raise ValueError with a readable message)
    def add(self, name, pw, role):
        name = (name or '').strip().lower()
        err = self.validate_name(name) or self.validate_password(pw, name)
        if err:
            raise ValueError(err)
        if role not in ROLES:
            raise ValueError('Role must be one of: ' + ', '.join(ROLES))
        with self.lock:
            if name in self.users:
                raise ValueError(f"User '{name}' already exists.")
            self.users[name] = {'role': role, **self._make_hash(pw)}
            self._save()

    def set_password(self, name, pw):
        err = self.validate_password(pw, name)
        if err:
            raise ValueError(err)
        with self.lock:
            if name not in self.users:
                raise ValueError(f"No such user '{name}'.")
            self.users[name].update(self._make_hash(pw))
            self._save()

    def set_role(self, name, role):
        if role not in ROLES:
            raise ValueError('Role must be one of: ' + ', '.join(ROLES))
        with self.lock:
            if name not in self.users:
                raise ValueError(f"No such user '{name}'.")
            self.users[name]['role'] = role
            self._save()

    def remove(self, name):
        with self.lock:
            if name not in self.users:
                raise ValueError(f"No such user '{name}'.")
            del self.users[name]
            self._save()

    def listing(self):
        with self.lock:
            return sorted((n, u.get('role', 'viewer')) for n, u in self.users.items())

    def verify(self, name, pw):
        """Returns the user's role if name+password are right, else None."""
        name = (name or '').strip().lower()
        with self.lock:
            rec = self.users.get(name)
        try:
            derived = self._derive(pw, rec or self._dummy)
            good = hmac.compare_digest(derived, bytes.fromhex((rec or self._dummy)['hash']))
        except (ValueError, KeyError, TypeError):
            return None
        return rec.get('role', 'viewer') if (rec and good) else None


def _jline(obj):
    return (json.dumps(obj, separators=(',', ':')) + '\n').encode('utf-8')


class LineBuf:
    """Collects bytes and yields complete JSON lines. Raises ValueError on
    oversized or malformed input, which makes the caller drop the connection."""
    def __init__(self):
        self.buf = b''

    def feed(self, data):
        self.buf += data
        out = []
        while b'\n' in self.buf:
            line, self.buf = self.buf.split(b'\n', 1)
            if len(line) > MAX_LINE:
                raise ValueError('line too long')
            if line.strip():
                msg = json.loads(line.decode('utf-8'))
                if not isinstance(msg, dict):
                    raise ValueError('not an object')
                out.append(msg)
        if len(self.buf) > MAX_LINE:
            raise ValueError('line too long')
        return out


class _Conn:
    """One logged-in client, as seen by the server."""
    def __init__(self, cid, user, role, addr):
        self.id, self.user, self.role, self.addr = cid, user, role, addr
        self.out = queue.Queue()
        self.alive = True
        self.last_rx = time.time()
        self.cmd_times = []
        self.cfg_hash = None
        self.last_push = 0.0
        self.last_state = None
        self.wsjt_ok = False       # unlocked WSJT control with the extra password
        self.wsjt_times = []


# ── WSJT-X / JTDX UDP stream ──
# WSJT-X and JTDX send their status/decodes as binary UDP datagrams (Qt
# QDataStream format, magic 0xADBCCBDA). They are passed on untouched, so every
# message type works and nothing needs decoding here; only the header is read,
# to validate the datagram and to remember the latest Heartbeat/Status per
# sender so a client that connects mid-session is brought up to date at once.
WSJT_PORT_DEFAULT = 2237
WSJT_MAGIC = b'\xad\xbc\xcb\xda'
WSJT_MAX_DGRAM = 16384       # real messages are far smaller; bigger ones are dropped
WSJT_QUEUE_MAX = 400         # per client: a stalled client loses datagrams instead of filling memory
# Message types a client may send back to the decoder: Clear 3, Reply 4, Replay 7, Halt Tx 8,
# Free text 9, Location 11, Highlight callsign 13. NOT allowed: Close 6, Switch configuration 14,
# Configure 15 (those would shut down or reconfigure the program).
WSJT_CTL_TYPES = frozenset({3, 4, 7, 8, 9, 11, 13})
WSJT_HALT_TX = 8             # safety command: never blocked by another client holding control
WSJT_MAX_RELAYS = 5          # copy targets for the incoming stream


def wsjt_peek(data):
    """(message type, sender id) of a WSJT-X UDP datagram, or None if it is not one."""
    if len(data) < 16 or data[:4] != WSJT_MAGIC:
        return None
    mtype = struct.unpack('>I', data[8:12])[0]
    n = struct.unpack('>I', data[12:16])[0]
    if mtype > 64:
        return None
    if n == 0xFFFFFFFF:
        return mtype, ''
    if n > len(data) - 16:
        return None
    return mtype, data[16:16 + n].decode('utf-8', 'replace')


def verify_ctl_password(pw, rec):
    """True if pw matches the stored scrypt record of the WSJT control password."""
    try:
        return bool(rec) and hmac.compare_digest(UserStore._derive(pw, rec), bytes.fromhex(rec['hash']))
    except (ValueError, KeyError, TypeError):
        return False


def wsjt_udp_sender(host):
    """UDP socket for sending to host: unicast as is; for a multicast group the
    TTL is 1 (stay on the LAN) and loopback stays on, so programs on this same PC
    that joined the group also receive it."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    if _is_multicast(host):
        s.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_TTL, 1)
        s.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_LOOP, 1)
    return s


def _is_multicast(host):
    try:
        return 224 <= int(host.split('.')[0]) <= 239
    except ValueError:
        return False


class WsjtListener:
    """Server side: receives the WSJT-X/JTDX UDP stream, optionally copies it to
    another local program, and hands every datagram to sink() (the clients)."""
    def __init__(self, app, sink):
        self.app, self.sink = app, sink
        self.sock = None
        self.thread = None
        self.error = ''
        self.listening = ''
        self.count = 0
        self.bad = 0
        self.sources = {}     # sender id -> ((ip, port), last seen): where replies must go
        self.relay_count = 0  # number of active copy targets
        self.relay_errs = 0   # failed sends to copy targets

    def log(self, msg):
        print('[wsjt] ' + msg)

    def start(self):
        self.stop()
        self.error = self.listening = ''
        wc = self.app.cfg.get('wsjt', {})
        if not wc.get('enabled'):
            return
        host = (wc.get('listen') or '127.0.0.1').strip()
        relays = []
        try:
            port = int(wc.get('port', WSJT_PORT_DEFAULT))
            for t in (wc.get('relays') or [])[:WSJT_MAX_RELAYS]:
                rh = str(t.get('host') or '').strip()
                if not rh:
                    continue
                rp = int(t.get('port'))
                if not 1 <= rp <= 65535:
                    raise ValueError(f'bad port {rp} for copy target {rh}')
                ip = socket.gethostbyname(rh)  # resolved once, not for every datagram
                if rp == port and ip in (host, '127.0.0.1', '0.0.0.0'):
                    raise ValueError(f'copy target {rh}:{rp} is the listen address (that would loop)')
                if (ip, rp) not in relays:
                    relays.append((ip, rp))
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            try:
                if _is_multicast(host):
                    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                    s.bind(('', port))
                    s.setsockopt(socket.IPPROTO_IP, socket.IP_ADD_MEMBERSHIP,
                                 socket.inet_aton(host) + socket.inet_aton('0.0.0.0'))
                else:
                    # no SO_REUSEADDR: on Windows it would let two programs share the port silently
                    s.bind((host, port))
                s.settimeout(0.5)
            except Exception:
                s.close()
                raise
        except (OSError, ValueError, TypeError) as e:
            self.error = str(e)
            self.log(f'cannot listen: {e}')
            return
        self.sock = s
        self.listening = f'{host}:{port}'
        self.relay_count, self.relay_errs = len(relays), 0
        self.thread = threading.Thread(target=self._loop, args=(s, relays), daemon=True)
        self.thread.start()
        self.log(f'listening on {self.listening}' + (', copying to ' + ', '.join(f'{h}:{p}' for h, p in relays) if relays else ''))

    def stop(self):
        s, self.sock = self.sock, None
        if s:
            try:
                s.close()
            except OSError:
                pass
        t = self.thread
        if t and t is not threading.current_thread():
            t.join(2.0)
        self.thread = None
        self.listening = ''

    def send_to_decoder(self, data):
        """Send a datagram back to the WSJT-X/JTDX instance it is addressed to (by sender id).
        Only addresses learned from that program's own traffic are ever used. -> (ok, reason)"""
        info = wsjt_peek(data)
        s = self.sock
        if not s or info is None:
            return False, 'WSJT listener not running'
        rec = self.sources.get(info[1])
        if not rec or time.time() - rec[1] > 60:
            return False, f'WSJT-X/JTDX "{info[1]}" not seen recently'
        try:
            s.sendto(data, rec[0])
        except OSError as e:
            return False, str(e)
        return True, ''

    def _loop(self, s, relays):
        outs = [(wsjt_udp_sender(h), (h, p)) for h, p in relays]  # unicast or multicast, each as needed
        try:
            while self.sock is s:
                try:
                    data, addr = s.recvfrom(65535)
                except socket.timeout:
                    continue
                except ConnectionResetError:
                    continue
                except OSError:
                    break
                info = wsjt_peek(data) if len(data) <= WSJT_MAX_DGRAM else None
                if info is None:
                    self.bad += 1
                    continue
                self.count += 1
                if info[1] in self.sources or len(self.sources) < 16:
                    self.sources[info[1]] = (addr, time.time())
                for o, target in outs:
                    try:
                        o.sendto(data, target)
                    except OSError:
                        self.relay_errs += 1
                try:
                    self.sink(data)
                except Exception as e:  # noqa: BLE001
                    self.log(f'sink error: {e}')
        finally:
            for o, _target in outs:
                o.close()


class RemoteServer:
    COMMANDS = ('select_dir', 'toggle_aux', 'all_off')

    def __init__(self, app):
        self.app = app
        self.clients = {}
        self.lock = threading.Lock()
        self.running = False
        self.error = ''
        self.listener = None
        self.accept_thread = None
        self.ctx = None
        self.fail = {}                # ip -> {'times': [...], 'until': ts}
        self.controller_id = None
        self.controller_ts = 0.0
        self.next_id = 1
        self.pending = 0              # connections that have not logged in yet
        self.last_state_json = None
        self.wsjt_cache = {}          # (type, sender id) -> latest Heartbeat/Status line

    # ---- logging (console + station_server.log, with size-based rotation)
    def log(self, msg):
        line = time.strftime('%Y-%m-%d %H:%M:%S ') + msg
        print('[server] ' + line)
        try:
            path = side_file('station_server.log')
            if os.path.exists(path) and os.path.getsize(path) > 1_000_000:
                os.replace(path, path + '.1')
            with open(path, 'a', encoding='utf-8') as f:
                f.write(line + '\n')
        except OSError:
            pass

    @property
    def cfg(self):
        return self.app.cfg.get('remote', {})

    # ---- lifecycle
    def start(self):
        self.stop()
        self.error = ''
        cert, key = side_file('station_cert.pem'), side_file('station_key.pem')
        try:
            if not (os.path.exists(cert) and os.path.exists(key)):
                self.log('No certificate found, generating a self-signed one')
                generate_certificate(cert, key)
            ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            ctx.minimum_version = ssl.TLSVersion.TLSv1_2
            ctx.load_cert_chain(cert, key)
            lst = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            lst.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            lst.bind((self.cfg.get('sBind', '0.0.0.0') or '0.0.0.0',
                      int(self.cfg.get('sPort', REMOTE_PORT_DEFAULT))))
            lst.listen(16)
            lst.settimeout(0.5)
        except Exception as e:
            self.error = str(e)
            self.log(f'Cannot start server: {e}')
            raise
        self.ctx, self.listener, self.running = ctx, lst, True
        self.accept_thread = threading.Thread(target=self._accept_loop, args=(lst,), daemon=True)
        self.accept_thread.start()
        self.log(f'Listening on {lst.getsockname()[0]}:{lst.getsockname()[1]} '
                 f'(certificate {fmt_fingerprint(cert_fingerprint(cert) or "")[:23]}...)')

    def stop(self):
        was = self.running
        self.running = False
        if self.listener:
            try:
                self.listener.close()
            except OSError:
                pass
            self.listener = None
        with self.lock:
            for c in list(self.clients.values()):
                c.alive = False
        t = self.accept_thread
        if t and t is not threading.current_thread():
            t.join(2.0)  # the old listener must be fully closed before the port can be bound again
        self.accept_thread = None
        if was:
            self.log('Server stopped')

    def port(self):
        try:
            return self.listener.getsockname()[1]
        except (OSError, AttributeError):
            return None

    # ---- lockout bookkeeping
    def _locked_out(self, ip):
        rec = self.fail.get(ip)
        return bool(rec and rec['until'] > time.time())

    def _note_failure(self, ip, user):
        now = time.time()
        rec = self.fail.setdefault(ip, {'times': [], 'until': 0})
        rec['times'] = [t for t in rec['times'] if now - t < LOCKOUT_WINDOW_S] + [now]
        self.log(f"LOGIN FAILED user='{user[:32]}' from {ip} ({len(rec['times'])}/{LOCKOUT_FAILS})")
        if len(rec['times']) >= LOCKOUT_FAILS:
            rec['until'] = now + LOCKOUT_S
            rec['times'] = []
            self.log(f'LOCKOUT {ip} for {LOCKOUT_S // 60} min after {LOCKOUT_FAILS} failed logins')
        if len(self.fail) > 500:  # keep the table bounded
            for k in [k for k, v in self.fail.items() if v['until'] < now and not v['times']][:250]:
                self.fail.pop(k, None)

    # ---- accepting
    def _accept_loop(self, lst):
        while self.running and lst is self.listener:
            try:
                raw, addr = lst.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            if self._locked_out(addr[0]) or self.pending >= 30:
                try:
                    raw.close()  # dropped before any TLS work is spent on it
                except OSError:
                    pass
                continue
            threading.Thread(target=self._handle, args=(raw, addr), daemon=True).start()

    @staticmethod
    def _read_one(sock, buf, deadline):
        while time.time() < deadline:
            try:
                data = sock.recv(4096)
            except (socket.timeout, TimeoutError):
                continue
            if not data:
                return None
            msgs = buf.feed(data)
            if msgs:
                return msgs[0]
        return None

    def _handle(self, raw, addr):
        ip = addr[0]
        conn = None
        sock = None
        self.pending += 1
        counted = True
        try:
            raw.settimeout(10)
            try:
                sock = self.ctx.wrap_socket(raw, server_side=True)
            except (ssl.SSLError, OSError):
                return  # not TLS, or a failed handshake: just drop it
            sock.settimeout(1.0)
            buf = LineBuf()
            msg = self._read_one(sock, buf, time.time() + 10)
            if not msg or msg.get('t') != 'login':
                return
            user = str(msg.get('user', ''))[:64]
            pw = str(msg.get('pw', ''))[:MAX_PW_LEN + 64]
            role = self.users().verify(user, pw)
            if role is None:
                self._note_failure(ip, user)
                time.sleep(1.0)  # slows guessing on every single attempt
                sock.sendall(_jline({'t': 'login_fail', 'reason': 'Login failed'}))
                return
            with self.lock:
                full = len(self.clients) >= MAX_CLIENTS
                if not full:
                    cid = self.next_id
                    self.next_id += 1
                    conn = _Conn(cid, user.strip().lower(), role, ip)
                    self.clients[cid] = conn
            if full:
                sock.sendall(_jline({'t': 'login_fail', 'reason': 'Server is full'}))
                return
            self.fail.pop(ip, None)
            self.pending -= 1
            counted = False
            self.log(f"LOGIN OK user='{conn.user}' role={role} from {ip}")
            conn.out.put(_jline({'t': 'login_ok', 'role': role, 'user': conn.user,
                                 'ver': APP_VERSION}))
            for line in self.wsjt_snapshot():  # bring a late joiner up to date
                conn.out.put(line)
            self._serve(sock, conn, buf)
        except Exception as e:  # a bad client must never take the server down
            self.log(f'connection error from {ip}: {e}')
        finally:
            if counted:
                self.pending -= 1
            if conn:
                self._drop(conn)
            try:
                (sock or raw).close()
            except OSError:
                pass

    def users(self):
        return self.app.users

    def _serve(self, sock, conn, buf):
        sock.settimeout(0.2)
        while self.running and conn.alive:
            data = None
            try:
                data = sock.recv(4096)
                if data == b'':
                    break
            except (socket.timeout, TimeoutError):
                pass
            except OSError:
                break
            now = time.time()
            if data:
                conn.last_rx = now
                try:
                    for msg in buf.feed(data):
                        self._on_msg(conn, msg)
                except ValueError:
                    self.log(f"bad message from '{conn.user}', disconnecting")
                    break
            if now - conn.last_rx > LINK_TIMEOUT_S:
                self.log(f"'{conn.user}' timed out")
                break
            try:
                sock.settimeout(5)  # sends get a longer timeout than the polling reads
                while True:
                    sock.sendall(conn.out.get_nowait())
            except queue.Empty:
                pass
            except OSError:
                break
            finally:
                sock.settimeout(0.2)

    def _drop(self, conn):
        conn.alive = False
        with self.lock:
            self.clients.pop(conn.id, None)
            if self.controller_id == conn.id:
                self.controller_id = None
        self.log(f"'{conn.user}' disconnected")

    # ---- messages from a client
    def _ack(self, conn, mid, ok, reason=''):
        conn.out.put(_jline({'t': 'ack', 'id': mid, 'ok': ok, 'reason': reason}))

    def _on_msg(self, conn, msg):
        t = msg.get('t')
        if t == 'ping':
            conn.out.put(_jline({'t': 'pong'}))
        elif t == 'cmd':
            self._on_cmd(conn, msg)
        elif t == 'wsjt_auth':
            self._on_wsjt_auth(conn, msg)
        elif t == 'wsjt_cmd':
            self._on_wsjt_cmd(conn, msg)

    # ---- WSJT-X / JTDX remote control: needs an operator/admin login AND the extra password
    def _on_wsjt_auth(self, conn, msg):
        wc = self.app.cfg.get('wsjt', {})
        if conn.role == 'viewer' or not wc.get('ctlEnabled') or not wc.get('ctlHash'):
            self.log(f"WSJT control refused for '{conn.user}': not available")
            conn.out.put(_jline({'t': 'wsjt_auth_fail', 'reason': 'Remote WSJT control is not available for this account'}))
            return
        pw = str(msg.get('pw', ''))[:MAX_PW_LEN + 64]
        if verify_ctl_password(pw, wc['ctlHash']):
            conn.wsjt_ok = True
            self.log(f"'{conn.user}' unlocked WSJT control")
            conn.out.put(_jline({'t': 'wsjt_auth_ok'}))
            return
        conn.wsjt_ok = False
        self._note_failure(conn.addr, conn.user + ' (WSJT control password)')
        time.sleep(1.0)
        conn.out.put(_jline({'t': 'wsjt_auth_fail', 'reason': 'Wrong WSJT control password'}))
        if self._locked_out(conn.addr):
            conn.alive = False

    def _on_wsjt_cmd(self, conn, msg):
        wc = self.app.cfg.get('wsjt', {})
        if not (wc.get('ctlEnabled') and conn.wsjt_ok) or conn.role == 'viewer':
            return self._deny(conn, None, 'wsjt', 'WSJT control is locked')
        now = time.time()
        conn.wsjt_times = [t for t in conn.wsjt_times if now - t < 2.0] + [now]
        if len(conn.wsjt_times) > 10:
            return self._deny(conn, None, 'wsjt', 'Too many WSJT commands, slow down')
        try:
            data = base64.b64decode(msg.get('d'), validate=True)
        except (ValueError, TypeError):
            return self._deny(conn, None, 'wsjt', 'Bad WSJT message')
        info = wsjt_peek(data) if len(data) <= WSJT_MAX_DGRAM else None
        if info is None:
            return self._deny(conn, None, 'wsjt', 'Bad WSJT message')
        mtype = info[0]
        if mtype not in WSJT_CTL_TYPES:
            return self._deny(conn, None, f'wsjt:{mtype}', 'This WSJT message type is not allowed')
        if mtype != WSJT_HALT_TX:  # Halt Tx always goes through; the rest follows the single-controller rule
            with self.lock:
                holder = self.clients.get(self.controller_id)
                idle = now - self.controller_ts >= CONTROL_IDLE_S
                if holder and holder.id != conn.id and not idle:
                    if conn.role != 'admin':
                        return self._deny(conn, None, f'wsjt:{mtype}', f'Controlled by {holder.user}')
                    self.log(f"admin '{conn.user}' takes control from '{holder.user}'")
                self.controller_id, self.controller_ts = conn.id, now
        wl = self.app.wsjt
        ok, reason = wl.send_to_decoder(data) if wl else (False, 'WSJT listener not running')
        if ok:
            self.log(f"'{conn.user}' WSJT message type {mtype} -> '{info[1]}'")
        else:
            self._deny(conn, None, f'wsjt:{mtype}', reason)

    def controller_name(self):
        """Who currently holds control (None if nobody, or if they have gone idle)."""
        with self.lock:
            c = self.clients.get(self.controller_id)
            if c and time.time() - self.controller_ts < CONTROL_IDLE_S:
                return c.user
        return None

    def _on_cmd(self, conn, msg):
        mid, cmd = msg.get('id'), msg.get('cmd')
        if conn.role == 'viewer':
            return self._deny(conn, mid, cmd, 'View-only account')
        now = time.time()
        conn.cmd_times = [t for t in conn.cmd_times if now - t < 2.0] + [now]
        if len(conn.cmd_times) > 12:
            return self._deny(conn, mid, cmd, 'Too many commands, slow down')
        args = {}
        if cmd == 'select_dir':
            d = msg.get('dir')
            if d not in self.app.cfg.get('arrayDirs', []):
                return self._deny(conn, mid, cmd, 'Unknown direction')
            args = {'dir': d}
        elif cmd == 'toggle_aux':
            i = msg.get('idx')
            n_aux = 8 - self.app.cfg.get('switchRelays', 4)
            if not isinstance(i, int) or isinstance(i, bool) or not (0 <= i < n_aux):
                return self._deny(conn, mid, cmd, 'Unknown aux relay')
            args = {'idx': i}
        elif cmd != 'all_off':
            return self._deny(conn, mid, cmd, 'Unknown command')
        with self.lock:  # single controller at a time
            holder = self.clients.get(self.controller_id)
            idle = now - self.controller_ts >= CONTROL_IDLE_S
            if holder and holder.id != conn.id and not idle:
                if conn.role != 'admin':
                    return self._deny(conn, mid, cmd, f'Controlled by {holder.user}', locked=True)
                self.log(f"admin '{conn.user}' takes control from '{holder.user}'")
            self.controller_id, self.controller_ts = conn.id, now
        self.app.ui_q.put(lambda: self._execute(conn, mid, cmd, args))

    def _deny(self, conn, mid, cmd, reason, locked=False):
        self.log(f"DENIED '{conn.user}' {cmd}: {reason}")
        self._ack(conn, mid, False, reason)

    def _execute(self, conn, mid, cmd, args):
        """Runs on the UI thread, the same way a click in the server's window would."""
        app = self.app
        if app._busy:
            return self._deny(conn, mid, cmd, 'Busy, try again')
        if app._tx_blocked_cached():
            return self._deny(conn, mid, cmd, app.TX_BLOCK_MSG)
        self.log(f"'{conn.user}' {cmd} {args or ''}".rstrip())
        self._ack(conn, mid, True)
        if cmd == 'select_dir':
            app.select_dir(args['dir'])
        elif cmd == 'toggle_aux':
            app.toggle_aux(args['idx'])
        else:
            app.all_off()

    # ---- messages to the clients (called from the UI thread)
    def broadcast_event(self, text, err=False):
        data = _jline({'t': 'event', 'msg': text, 'err': bool(err)})
        with self.lock:
            for c in self.clients.values():
                c.out.put(data)

    def broadcast_wsjt(self, data):
        """Pass one WSJT-X/JTDX datagram on to every logged-in client (called from the listener thread)."""
        info = wsjt_peek(data)
        if info is None:
            return
        mtype, wid = info
        line = _jline({'t': 'wsjt', 'd': base64.b64encode(data).decode('ascii')})
        with self.lock:
            if mtype in (0, 1):  # Heartbeat / Status
                if len(self.wsjt_cache) < 16 or (mtype, wid) in self.wsjt_cache:
                    self.wsjt_cache[(mtype, wid)] = line
            elif mtype == 6:     # Close
                self.wsjt_cache.pop((0, wid), None)
                self.wsjt_cache.pop((1, wid), None)
            for c in self.clients.values():
                if c.out.qsize() < WSJT_QUEUE_MAX:
                    c.out.put(line)

    def wsjt_snapshot(self):
        with self.lock:
            return list(self.wsjt_cache.values())

    def push_state(self, state, cfg_view):
        """state: dict from the app. Sent when it changed, or as a heartbeat."""
        now = time.time()
        with self.lock:
            conns = list(self.clients.values())
        names = sorted({c.user for c in conns})
        state = dict(state, ctl=self.controller_name(), clients=names)
        base = json.dumps(state, sort_keys=True)
        cfg_hash = hashlib.sha1(json.dumps(cfg_view, sort_keys=True).encode()).hexdigest()
        for c in conns:
            if base == c.last_state and cfg_hash == c.cfg_hash and now - c.last_push < HEARTBEAT_S:
                continue
            m = dict(state, t='state')
            if c.cfg_hash != cfg_hash:
                m['cfg'] = cfg_view
                c.cfg_hash = cfg_hash
            c.last_state, c.last_push = base, now
            c.out.put(_jline(m))
        return names



class RemoteClient:
    """Network side of client mode. Runs in its own thread and talks to the UI
    only through app.ui_q (callables run on the UI thread)."""
    def __init__(self, app):
        self.app = app
        self.stop_ev = threading.Event()
        self.thread = None
        self.out = queue.Queue()
        self.state = 'stopped'  # connecting / connected / disconnected / auth-failed / cert-mismatch
        self.next_id = 1
        self.session_pw = None  # password typed this session when "remember" is off
        self.wsjt_ok = False      # WSJT control unlocked on the server for this connection
        self.wsjt_blocked = False  # server refused the control password: do not retry (lockout risk)

    # ---- control
    def start(self):
        self.stop()
        self.stop_ev = threading.Event()
        self.thread = threading.Thread(target=self._run, args=(self.stop_ev,), daemon=True)
        self.thread.start()

    def stop(self):
        self.stop_ev.set()
        self.state = 'stopped'

    def send_cmd(self, cmd, **args):
        self.out.put(_jline(dict(t='cmd', id=self.next_id, cmd=cmd, **args)))
        self.next_id += 1

    def send_wsjt(self, data):
        self.out.put(_jline({'t': 'wsjt_cmd', 'd': base64.b64encode(data).decode('ascii')}))

    def _wsjt_auth(self):
        """Ask the server to unlock WSJT control (once per connection)."""
        wc = self.app.cfg.get('wsjt', {})
        self.wsjt_ok = False
        if not wc.get('ctlEnabled') or self.wsjt_blocked:
            return
        pw = wc.get('ctlPassword') or self.app._wsjt_pw
        if pw:
            self.out.put(_jline({'t': 'wsjt_auth', 'pw': pw}))

    def _link(self, state, detail=''):
        self.state = state
        self.app.ui_q.put(lambda: self.app._remote_link(state, detail))

    # ---- connection loop with back-off
    def _run(self, stop_ev):
        delay = 2
        while not stop_ev.is_set():
            self.wsjt_ok = False
            self._link('connecting')
            try:
                self._session(stop_ev)
                delay = 2
            except _FatalLink as e:      # wrong password / changed certificate: don't retry and risk a lockout
                self._link(e.state, str(e))
                return
            except Exception as e:
                self._link('disconnected', str(e))
            if stop_ev.wait(delay):
                return
            delay = min(delay * 2, 30)

    def _session(self, stop_ev):
        rc = dict(self.app.cfg.get('remote', {}))
        host, port, user = rc.get('cHost', ''), int(rc.get('cPort', REMOTE_PORT_DEFAULT)), rc.get('cUser', '')
        if not host or not user:
            raise _FatalLink('disconnected', 'Set the server address and user name in Remote settings.')
        pw = rc.get('cPassword', '') if rc.get('cRemember') else self.session_pw
        if not pw:
            pw = self._ask_password(user, host)
            if not pw:
                raise _FatalLink('auth-failed', 'No password entered.')
            self.session_pw = pw
        raw = socket.create_connection((host, port), timeout=8)
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        ctx.minimum_version = ssl.TLSVersion.TLSv1_2
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE  # identity is checked by the pinned fingerprint instead
        sock = ctx.wrap_socket(raw)
        try:
            fp = hashlib.sha256(sock.getpeercert(binary_form=True)).hexdigest().upper()
            pinned = (rc.get('cFingerprint') or '').replace(':', '').upper()
            if pinned:
                if not hmac.compare_digest(pinned, fp):
                    raise _FatalLink('cert-mismatch', fp)
            elif self._ask_trust(fp, host):
                self.app.ui_q.put(lambda: self.app._remote_pin(fp))
            else:
                raise _FatalLink('cert-mismatch', 'Server certificate not trusted.')
            sock.settimeout(0.2)
            sock.sendall(_jline({'t': 'login', 'user': user, 'pw': pw}))
            self._loop(sock, stop_ev)
        finally:
            try:
                sock.close()
            except OSError:
                pass

    def _loop(self, sock, stop_ev):
        buf, last_rx, last_ping = LineBuf(), time.time(), 0.0
        while not self.out.empty():  # commands queued for an old connection are stale
            self.out.get_nowait()
        while not stop_ev.is_set():
            data = None
            try:
                data = sock.recv(8192)
                if data == b'':
                    raise ConnectionError('Server closed the connection')
            except (socket.timeout, TimeoutError):
                pass
            now = time.time()
            if data:
                last_rx = now
                for msg in buf.feed(data):
                    self._on_msg(msg)
            if now - last_rx > LINK_TIMEOUT_S:
                raise ConnectionError('No data from the server (link lost)')
            if now - last_ping > HEARTBEAT_S:
                self.out.put(_jline({'t': 'ping'}))
                last_ping = now
            try:
                sock.settimeout(5)
                while True:
                    sock.sendall(self.out.get_nowait())
            except queue.Empty:
                pass
            finally:
                sock.settimeout(0.2)

    def _on_msg(self, msg):
        t, app = msg.get('t'), self.app
        if t == 'login_ok':
            self._link('connected', f"{msg.get('user')} ({msg.get('role')})")
            app.ui_q.put(lambda: app._remote_set_role(msg.get('role')))
            self._wsjt_auth()
        elif t == 'login_fail':
            raise _FatalLink('auth-failed', msg.get('reason', 'Login failed'))
        elif t == 'state':
            app.ui_q.put(lambda: app._remote_apply_state(msg))
        elif t == 'event':
            app.ui_q.put(lambda: app.toast(str(msg.get('msg', '')), err=bool(msg.get('err'))))
        elif t == 'wsjt':
            app.wsjt_emit(msg.get('d'))  # plain UDP send, safe from this thread
        elif t == 'wsjt_auth_ok':
            self.wsjt_ok = True
            app.ui_q.put(lambda: app.toast('WSJT control unlocked'))
        elif t == 'wsjt_auth_fail':
            self.wsjt_ok, self.wsjt_blocked = False, True
            reason = str(msg.get('reason', 'refused'))
            app.ui_q.put(lambda: app.toast('WSJT control: ' + reason, err=True))
        elif t == 'ack' and not msg.get('ok'):
            reason = str(msg.get('reason', 'refused'))
            app.ui_q.put(lambda: app.toast(reason, err=True))

    # ---- questions for the user (answered on the UI thread)
    def _ask(self, fn, timeout=300):
        ev, res = threading.Event(), []
        self.app.ui_q.put(lambda: (res.append(fn()), ev.set()))
        ev.wait(timeout)
        return res[0] if res else None

    def _ask_password(self, user, host):
        return self._ask(lambda: self.app._remote_ask_password(user, host))

    def _ask_trust(self, fp, host):
        return bool(self._ask(lambda: self.app._remote_ask_trust(fp, host)))


class _FatalLink(Exception):
    def __init__(self, state, detail=''):
        super().__init__(detail)
        self.state = state


class UserDialog(tk.Toplevel):
    """Add a user, or (with name given) change that user's password and role."""
    def __init__(self, parent, store, name=None, role='operator'):
        super().__init__(parent)
        self.store, self.edit, self.result = store, name, False
        self.title('Change user' if name else 'Add user')
        self.transient(parent)
        self.resizable(True, True)
        sf = ScrollFrame(self, stretch=True)
        sf.pack(fill='both', expand=True)
        root = sf.inner
        pad = {'padx': 8, 'pady': 4}
        self.v_name = tk.StringVar(value=name or '')
        self.v_pw = tk.StringVar()
        self.v_pw2 = tk.StringVar()
        self.v_role = tk.StringVar(value=role)
        ttk.Label(root, text='User name').grid(row=0, column=0, sticky='w', **pad)
        e = ttk.Entry(root, textvariable=self.v_name, width=24, state='disabled' if name else 'normal')
        e.grid(row=0, column=1, **pad)
        ttk.Label(root, text='Password').grid(row=1, column=0, sticky='w', **pad)
        ttk.Entry(root, textvariable=self.v_pw, show='*', width=24).grid(row=1, column=1, **pad)
        ttk.Label(root, text='Repeat').grid(row=2, column=0, sticky='w', **pad)
        ttk.Entry(root, textvariable=self.v_pw2, show='*', width=24).grid(row=2, column=1, **pad)
        ttk.Label(root, text='Role').grid(row=3, column=0, sticky='w', **pad)
        ttk.Combobox(root, textvariable=self.v_role, values=list(ROLES), state='readonly',
                     width=21).grid(row=3, column=1, **pad)
        ttk.Label(root, foreground='#666', justify='left',
                  text=f'At least {MIN_PW_LEN} characters. viewer = display only,\n'
                       'operator = can switch, admin = can also take control.'
                  ).grid(row=4, column=0, columnspan=2, sticky='w', **pad)
        bar = ttk.Frame(root)
        bar.grid(row=5, column=0, columnspan=2, sticky='e', **pad)
        ttk.Button(bar, text='OK', command=self._ok).pack(side='left', padx=4)
        ttk.Button(bar, text='Cancel', command=self.destroy).pack(side='left')
        self.bind('<Return>', lambda e: self._ok())
        self.grab_set()
        self.wait_visibility()

    def _ok(self):
        name = self.v_name.get().strip().lower()
        pw, pw2 = self.v_pw.get(), self.v_pw2.get()
        if pw != pw2:
            messagebox.showerror('Passwords differ', 'The two passwords are not the same.', parent=self)
            return
        try:
            if self.edit:
                self.store.set_role(name, self.v_role.get())
                self.store.set_password(name, pw)
            else:
                self.store.add(name, pw, self.v_role.get())
        except ValueError as e:
            messagebox.showerror('Cannot save', str(e), parent=self)
            return
        self.result = True
        self.destroy()


class RemoteDialog(tk.Toplevel):
    """Remote menu -> Server / client settings."""
    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title('Remote: server / client')
        self.transient(app)
        sf = ScrollFrame(self, stretch=True)
        sf.pack(fill='both', expand=True)
        root = sf.inner
        root.columnconfigure(0, weight=1, uniform='col')
        root.columnconfigure(1, weight=1, uniform='col')
        rc = app.cfg.setdefault('remote', {})
        pad = {'padx': 6, 'pady': 3}

        mode = ttk.LabelFrame(root, text='This program runs as')
        mode.grid(row=0, column=0, sticky='nsew', padx=(8, 4), pady=(8, 4))
        self.v_mode = tk.StringVar(value=app.cfg.get('appMode', 'standalone'))
        for val, txt in (('standalone', 'Standalone  (everything on this PC, as before)'),
                         ('server', 'Server  (at the station: controls CAT + relays, serves clients)'),
                         ('client', 'Client  (remote: shows the station and sends commands)')):
            ttk.Radiobutton(mode, text=txt, value=val, variable=self.v_mode).pack(anchor='w', **pad)
        ttk.Label(mode, foreground='#666', text='Changing this takes effect after restarting the program.'
                  ).pack(anchor='w', **pad)

        # ---- server
        sv = ttk.LabelFrame(root, text='Server')
        sv.grid(row=1, column=0, sticky='nsew', padx=(8, 4), pady=4)
        self.v_bind = tk.StringVar(value=rc.get('sBind', '0.0.0.0'))
        self.v_sport = tk.StringVar(value=str(rc.get('sPort', REMOTE_PORT_DEFAULT)))
        ttk.Label(sv, text='Listen on').grid(row=0, column=0, sticky='w', **pad)
        ttk.Entry(sv, textvariable=self.v_bind, width=16).grid(row=0, column=1, sticky='w', **pad)
        ttk.Label(sv, text='Port').grid(row=0, column=2, sticky='w', **pad)
        ttk.Entry(sv, textvariable=self.v_sport, width=7).grid(row=0, column=3, sticky='w', **pad)
        self.lbl_status = ttk.Label(sv, text='')
        self.lbl_status.grid(row=1, column=0, columnspan=4, sticky='w', **pad)
        ttk.Label(sv, text='Certificate\nfingerprint').grid(row=2, column=0, sticky='w', **pad)
        self.v_fp = tk.StringVar()
        self.txt_fp = tk.Text(sv, height=2, width=50, font=('Courier New', 8), wrap='char',
                              relief='flat', bg=self.cget('bg'), state='disabled')
        self.txt_fp.grid(row=2, column=1, columnspan=2, sticky='w', **pad)
        ttk.Button(sv, text='Copy', width=6, command=self._copy_fp).grid(row=2, column=3, sticky='w', **pad)
        ttk.Button(sv, text='Generate new certificate', command=self._gen_cert).grid(
            row=3, column=0, columnspan=2, sticky='w', **pad)
        ttk.Label(sv, foreground='#666', text='Give clients this fingerprint to compare on first connect.'
                  ).grid(row=3, column=2, columnspan=2, sticky='w', **pad)
        ttk.Label(sv, text='Users').grid(row=4, column=0, sticky='nw', **pad)
        uf = ttk.Frame(sv)
        uf.grid(row=4, column=1, columnspan=3, sticky='ew', **pad)
        self.users_list = tk.Listbox(uf, height=5, exportselection=False, width=30)
        self.users_list.pack(side='left', fill='y')
        ub = ttk.Frame(uf)
        ub.pack(side='left', padx=6, anchor='n')
        for txt, cmd in (('Add...', self._add_user), ('Change password / role...', self._edit_user),
                         ('Remove', self._remove_user)):
            ttk.Button(ub, text=txt, command=cmd).pack(fill='x', pady=1)
        self.lbl_clients = ttk.Label(sv, text='')
        self.lbl_clients.grid(row=5, column=0, columnspan=4, sticky='w', **pad)

        # ---- client
        cl = ttk.LabelFrame(root, text='Client: the server to connect to')
        cl.grid(row=0, column=1, sticky='nsew', padx=(4, 8), pady=(8, 4))
        self.v_chost = tk.StringVar(value=rc.get('cHost', ''))
        self.v_cport = tk.StringVar(value=str(rc.get('cPort', REMOTE_PORT_DEFAULT)))
        self.v_cuser = tk.StringVar(value=rc.get('cUser', ''))
        self.v_cpw = tk.StringVar(value=rc.get('cPassword', ''))
        self.v_cremember = tk.BooleanVar(value=bool(rc.get('cRemember', True)))
        self.v_cfp = tk.StringVar(value=fmt_fingerprint(rc.get('cFingerprint', '')))
        ttk.Label(cl, text='Server').grid(row=0, column=0, sticky='w', **pad)
        ttk.Entry(cl, textvariable=self.v_chost, width=26).grid(row=0, column=1, sticky='w', **pad)
        ttk.Label(cl, text='Port').grid(row=0, column=2, sticky='w', **pad)
        ttk.Entry(cl, textvariable=self.v_cport, width=7).grid(row=0, column=3, sticky='w', **pad)
        ttk.Label(cl, text='User').grid(row=1, column=0, sticky='w', **pad)
        ttk.Entry(cl, textvariable=self.v_cuser, width=26).grid(row=1, column=1, sticky='w', **pad)
        ttk.Label(cl, text='Password').grid(row=2, column=0, sticky='w', **pad)
        ttk.Entry(cl, textvariable=self.v_cpw, show='*', width=26).grid(row=2, column=1, sticky='w', **pad)
        ttk.Checkbutton(cl, text='Remember password on this PC (stored in the settings file)',
                        variable=self.v_cremember).grid(row=3, column=0, columnspan=4, sticky='w', **pad)
        ttk.Label(cl, text='Pinned\nfingerprint').grid(row=4, column=0, sticky='w', **pad)
        ttk.Entry(cl, textvariable=self.v_cfp, width=60).grid(row=4, column=1, columnspan=3, sticky='ew', **pad)
        ttk.Label(cl, foreground='#666', justify='left', wraplength=600,
                  text='Leave empty to be asked on first connect, or paste the fingerprint shown on the  '
                       'server. Clear it if the server\'s certificate was regenerated on purpose.'
                  ).grid(row=5, column=0, columnspan=4, sticky='w', **pad)

        wc = app.cfg.setdefault('wsjt', dict(DEFAULT_CFG['wsjt']))
        wf = ttk.LabelFrame(root, text='WSJT-X / JTDX UDP stream')
        wf.grid(row=1, column=1, sticky='nsew', padx=(4, 8), pady=4)
        self.v_wen = tk.BooleanVar(value=bool(wc.get('enabled')))
        self.v_wlisten = tk.StringVar(value=wc.get('listen', '127.0.0.1'))
        self.v_wport = tk.StringVar(value=str(wc.get('port', WSJT_PORT_DEFAULT)))
        rl = list(wc.get('relays') or [])
        self.v_wrelays = []
        for i in range(WSJT_MAX_RELAYS):
            t = rl[i] if i < len(rl) else {}
            self.v_wrelays.append((tk.StringVar(value=str(t.get('host', ''))),
                                   tk.StringVar(value=str(t.get('port', 2238 + i)))))
        self.v_wohost = tk.StringVar(value=wc.get('outHost', '127.0.0.1'))
        self.v_woport = tk.StringVar(value=str(wc.get('outPort', WSJT_PORT_DEFAULT)))
        ttk.Checkbutton(wf, text='Enabled  (server: receive and send to clients  /  client: pass on to local programs)',
                        variable=self.v_wen).grid(row=0, column=0, columnspan=4, sticky='w', **pad)
        ttk.Label(wf, text='Server: listen on').grid(row=1, column=0, sticky='w', **pad)
        ttk.Entry(wf, textvariable=self.v_wlisten, width=16).grid(row=1, column=1, sticky='w', **pad)
        ttk.Label(wf, text='Port').grid(row=1, column=2, sticky='w', **pad)
        ttk.Entry(wf, textvariable=self.v_wport, width=7).grid(row=1, column=3, sticky='w', **pad)
        ttk.Label(wf, text='Server: also copy to\n(up to 5, empty = unused)', justify='left').grid(
            row=2, column=0, sticky='nw', **pad)
        rf = ttk.Frame(wf)
        rf.grid(row=2, column=1, columnspan=3, sticky='w')
        for i, (vh, vp) in enumerate(self.v_wrelays):
            ttk.Entry(rf, textvariable=vh, width=16).grid(row=i, column=0, sticky='w', padx=6, pady=1)
            ttk.Label(rf, text='Port').grid(row=i, column=1, padx=6)
            ttk.Entry(rf, textvariable=vp, width=7).grid(row=i, column=2, sticky='w', padx=6)
        ttk.Label(wf, text='Client: send to').grid(row=3, column=0, sticky='w', **pad)
        ttk.Entry(wf, textvariable=self.v_wohost, width=16).grid(row=3, column=1, sticky='w', **pad)
        ttk.Label(wf, text='Port').grid(row=3, column=2, sticky='w', **pad)
        ttk.Entry(wf, textvariable=self.v_woport, width=7).grid(row=3, column=3, sticky='w', **pad)
        ttk.Label(wf, foreground='#666', justify='left', wraplength=600,
                  text='Set WSJT-X/JTDX (Settings > Reporting > UDP Server) to the "listen on" address and port.  '
                       'All addresses can be unicast (e.g. 127.0.0.1) or multicast (e.g. 224.0.0.1 / 239.x.x.x).  '
                       '"Also copy to" forwards the incoming stream to up to 5 other programs/PCs (unicast or multicast).  '
                       'Clients receive the stream from the server over the secure link and send it out locally.  '
                       'Remote control (clients answering back) is a separate, password protected option below.'
                  ).grid(row=4, column=0, columnspan=4, sticky='w', **pad)
        self.lbl_wsjt = ttk.Label(wf, text='')
        self.lbl_wsjt.grid(row=5, column=0, columnspan=4, sticky='w', **pad)

        wk = ttk.LabelFrame(root, text='WSJT-X / JTDX remote control (client to server, extra password)')
        wk.grid(row=2, column=0, sticky='nsew', padx=(8, 4), pady=4)
        self.v_wcen = tk.BooleanVar(value=bool(wc.get('ctlEnabled')))
        self.v_wcpw = tk.StringVar(value=wc.get('ctlPassword', '') or app._wsjt_pw)
        ttk.Checkbutton(wk, text='Enabled  (server: accept control from clients  /  client: send replies back to the server)',
                        variable=self.v_wcen).grid(row=0, column=0, columnspan=3, sticky='w', **pad)
        ttk.Label(wk, text='Server: control password').grid(row=1, column=0, sticky='w', **pad)
        self.lbl_wpw = ttk.Label(wk, text='')
        self.lbl_wpw.grid(row=1, column=1, sticky='w', **pad)
        wbf = ttk.Frame(wk)
        wbf.grid(row=1, column=2, sticky='w', **pad)
        ttk.Button(wbf, text='Set...', width=7, command=self._set_ctl_pw).pack(side='left', padx=2)
        ttk.Button(wbf, text='Clear', width=7, command=self._clear_ctl_pw).pack(side='left')
        ttk.Label(wk, text='Client: control password').grid(row=2, column=0, sticky='w', **pad)
        ttk.Entry(wk, textvariable=self.v_wcpw, show='*', width=26).grid(row=2, column=1, columnspan=2, sticky='w', **pad)
        ttk.Label(wk, foreground='#666', justify='left', wraplength=600,
                  text='Lets the program on the client PC that receives the stream (WSJT-X, JTDX, GridTracker) answer  '
                       'to the WSJT-X/JTDX on the server PC: reply/call, halt Tx, free text, clear, replay, highlight.  '
                       'Needs an operator or admin login AND this extra password (min. 10 characters).  '
                       'Never passed on: close, configure, switch configuration. Halt Tx always goes through.'
                  ).grid(row=3, column=0, columnspan=3, sticky='w', **pad)
        self.lbl_wctl = ttk.Label(wk, text='')
        self.lbl_wctl.grid(row=4, column=0, columnspan=3, sticky='w', **pad)

        bot = ttk.Frame(root)
        bot.grid(row=2, column=1, sticky='nsew', padx=(4, 8), pady=4)
        self.v_min = tk.BooleanVar(value=bool(app.cfg.get('startMinimized')))
        ttk.Checkbutton(bot, text='Start minimized (server PC left running in the shack)',
                        variable=self.v_min).pack(anchor='w', padx=6, pady=2)
        bar = ttk.Frame(bot)
        bar.pack(side='bottom', fill='x', pady=(8, 4))
        ttk.Button(bar, text='Save & apply', command=self._save).pack(side='right', padx=4)
        ttk.Button(bar, text='Close', command=self.destroy).pack(side='right')
        self._refresh()

    # ---- server side helpers
    def _refresh(self):
        app = self.app
        self.users_list.delete(0, 'end')
        for name, role in app.users.listing():
            self.users_list.insert('end', f'{name}   [{role}]')
        fp = cert_fingerprint(side_file('station_cert.pem'))
        self.v_fp.set(fmt_fingerprint(fp) if fp else '(none yet, created when the server first starts)')
        self.txt_fp.config(state='normal')
        self.txt_fp.delete('1.0', 'end')
        self.txt_fp.insert('1.0', self.v_fp.get())
        self.txt_fp.config(state='disabled')
        srv = app.remote_server
        if srv and srv.running:
            self.lbl_status.config(text=f'Listening on port {srv.port()}', foreground='#080')
            names = ', '.join(sorted({c.user for c in list(srv.clients.values())})) or 'none'
            self.lbl_clients.config(text=f'Connected clients: {names}')
        elif srv and srv.error:
            self.lbl_status.config(text=f'Not listening: {srv.error}', foreground='#a00')
            self.lbl_clients.config(text='')
        else:
            self.lbl_status.config(text='Not running (mode is not "server")', foreground='#666')
            self.lbl_clients.config(text='')
        wl = app.wsjt
        if app.app_mode == 'client':
            txt, col = f'Passed on to local programs: {app.wsjt_out_count} datagrams', '#666'
        elif wl and wl.listening:
            txt = f'Listening on {wl.listening}: {wl.count} datagrams received' + \
                  (f', {wl.bad} ignored' if wl.bad else '') + \
                  (f', {wl.relay_count} copy target(s)' if wl.relay_count else '') + \
                  (f', {wl.relay_errs} copy send errors' if wl.relay_errs else '')
            col = '#080'
        elif wl and wl.error:
            txt, col = f'Not listening: {wl.error}', '#a00'
        else:
            txt, col = 'Not active', '#666'
        self.lbl_wsjt.config(text=txt, foreground=col)
        wcc = app.cfg.get('wsjt', {})
        self.lbl_wpw.config(text='set' if wcc.get('ctlHash') else 'not set',
                            foreground='#080' if wcc.get('ctlHash') else '#a00')
        rcl = app.remote_client
        if not wcc.get('ctlEnabled'):
            ctxt = 'Remote control: off'
        elif app.app_mode == 'client':
            ctxt = ('Remote control: unlocked' if rcl and rcl.wsjt_ok else
                    'Remote control: refused by the server (check the password, then Save & apply)'
                    if rcl and rcl.wsjt_blocked else 'Remote control: locked / waiting for the server')
        elif app.remote_server and app.remote_server.running:
            n = sum(1 for c in list(app.remote_server.clients.values()) if c.wsjt_ok)
            ctxt = f'Remote control: on, {n} client(s) unlocked'
        else:
            ctxt = 'Remote control: on (server not running)'
        self.lbl_wctl.config(text=ctxt)

    def _set_ctl_pw(self):
        pw = simpledialog.askstring('WSJT control password',
                                    f'New control password (at least {MIN_PW_LEN} characters):', show='*', parent=self)
        if pw is None:
            return
        if pw != simpledialog.askstring('WSJT control password', 'Repeat:', show='*', parent=self):
            messagebox.showerror('Passwords differ', 'The two passwords are not the same.', parent=self)
            return
        err = UserStore.validate_password(pw)
        if err:
            messagebox.showerror('Cannot save', err, parent=self)
            return
        self.app.cfg.setdefault('wsjt', {})['ctlHash'] = self.app.users._make_hash(pw)
        save_cfg(self.app.cfg)
        self._refresh()

    def _clear_ctl_pw(self):
        if messagebox.askyesno('WSJT control password', 'Remove the control password? Remote control stops working until a new one is set.', parent=self):
            self.app.cfg.setdefault('wsjt', {})['ctlHash'] = {}
            save_cfg(self.app.cfg)
            for c in list((self.app.remote_server.clients if self.app.remote_server else {}).values()):
                c.wsjt_ok = False
            self._refresh()

    def _copy_fp(self):
        self.clipboard_clear()
        self.clipboard_append(self.v_fp.get())

    def _selected_user(self):
        sel = self.users_list.curselection()
        return self.users_list.get(sel[0]).split()[0] if sel else None

    def _add_user(self):
        d = UserDialog(self, self.app.users)
        self.wait_window(d)
        self._refresh()

    def _edit_user(self):
        name = self._selected_user()
        if not name:
            return
        d = UserDialog(self, self.app.users, name=name, role=self.app.users.users[name].get('role', 'operator'))
        self.wait_window(d)
        self._refresh()

    def _remove_user(self):
        name = self._selected_user()
        if name and messagebox.askyesno('Remove user', f"Remove user '{name}'?", parent=self):
            self.app.users.remove(name)
            self._refresh()

    def _gen_cert(self):
        if not messagebox.askyesno(
                'New certificate',
                'Create a new certificate?\n\nEvery client will refuse to connect until its pinned '
                'fingerprint is cleared or updated.', parent=self):
            return
        try:
            generate_certificate(side_file('station_cert.pem'), side_file('station_key.pem'))
        except Exception as e:
            messagebox.showerror('Certificate', str(e), parent=self)
            return
        if self.app.remote_server and self.app.remote_server.running:
            self._start_server()
        self._refresh()

    def _start_server(self):
        try:
            self.app.remote_server.start()
        except Exception as e:
            messagebox.showerror('Server', f'Cannot start the server:\n{e}', parent=self)

    # ---- save
    def _save(self):
        app = self.app
        try:
            sport, cport = int(self.v_sport.get()), int(self.v_cport.get())
            if not (1 <= sport <= 65535 and 1 <= cport <= 65535):
                raise ValueError
        except ValueError:
            messagebox.showerror('Invalid', 'Ports must be numbers between 1 and 65535.', parent=self)
            return
        try:
            wport, woport = int(self.v_wport.get()), int(self.v_woport.get())
            if not (1 <= wport <= 65535 and 1 <= woport <= 65535):
                raise ValueError
        except ValueError:
            messagebox.showerror('Invalid', 'WSJT-X / JTDX ports must be numbers between 1 and 65535.', parent=self)
            return
        wrelays = []
        for vh, vp in self.v_wrelays:
            h = vh.get().strip()
            if not h:
                continue
            try:
                p = int(vp.get())
                if not 1 <= p <= 65535:
                    raise ValueError
            except ValueError:
                messagebox.showerror('Invalid', f'"Also copy to" {h}: the port must be a number between 1 and 65535.',
                                     parent=self)
                return
            wrelays.append({'host': h, 'port': p})
        mode = self.v_mode.get()
        if mode == 'client' and not (self.v_chost.get().strip() and self.v_cuser.get().strip()):
            messagebox.showerror('Invalid', 'Client mode needs a server address and a user name.', parent=self)
            return
        if mode == 'server' and self.v_wcen.get() and not app.cfg.get('wsjt', {}).get('ctlHash'):
            messagebox.showerror('Invalid', 'Set a WSJT control password first (Server: control password, Set...).', parent=self)
            return
        rc = app.cfg.setdefault('remote', {})
        rc.update(sBind=self.v_bind.get().strip() or '0.0.0.0', sPort=sport,
                  cHost=self.v_chost.get().strip(), cPort=cport, cUser=self.v_cuser.get().strip(),
                  cPassword=self.v_cpw.get() if self.v_cremember.get() else '',
                  cRemember=bool(self.v_cremember.get()),
                  cFingerprint=self.v_cfp.get().replace(':', '').replace(' ', '').upper())
        if not self.v_cremember.get() and app.remote_client:
            app.remote_client.session_pw = self.v_cpw.get() or None
        changed_mode = mode != app.app_mode
        app.cfg['appMode'] = mode
        app.cfg['startMinimized'] = bool(self.v_min.get())
        app.cfg['wsjt'] = {**app.cfg.get('wsjt', {}), 'enabled': bool(self.v_wen.get()),
                           'listen': self.v_wlisten.get().strip() or '127.0.0.1', 'port': wport,
                           'relays': wrelays,
                           'outHost': self.v_wohost.get().strip() or '127.0.0.1', 'outPort': woport}
        app.cfg['wsjt']['ctlEnabled'] = bool(self.v_wcen.get())
        app.cfg['wsjt']['ctlPassword'] = self.v_wcpw.get() if self.v_cremember.get() else ''
        app._wsjt_pw = self.v_wcpw.get()
        save_cfg(app.cfg)
        app.wsjt_apply()
        if app.app_mode == 'server' and app.remote_server and not changed_mode:
            self._start_server()      # new port/bind take effect now
        if app.app_mode == 'client' and app.remote_client and not changed_mode:
            app.remote_client.start()  # reconnect with the new settings
        app._update_title()
        if changed_mode:
            messagebox.showinfo('Restart needed', 'Restart the program to run in the new mode.', parent=self)
        self._refresh()


# ── Text of the Info menu (how everything works) ──
INFO_TOPICS = [
    ('Overview', """Stationcontroller controls via/with Hamlib, KMTronic relays and WSJT-X/JTDX.

It switches an antenna array (directions and aux relays) with a KMTronic 8-relay board, reads the radio's frequency and PTT through Hamlib's rigctld, sends the frequency to up to two COM ports, and relays the WSJT-X/JTDX UDP stream.

It runs in one of three modes (Remote menu, effective after a restart):
  Standalone  everything on this PC.
  Server      at the station: it alone talks to the relay board, rigctld, the COM ports and WSJT-X/JTDX, and serves clients over the internet.
  Client      on a remote PC: shows what the server reports and sends commands to it. No hardware access.

Menus: Run (main screen), View (what is shown), Array (array type), Output (COM ports), Hamlib (rigctld launcher), Remote (server/client), Set (settings), Info (this text)."""),

    ('Relays and arrays', """Relays: a KMTronic board is driven over UDP (classic board, port 12345, no login) or HTTP (web board). Relays 1..n switch the direction, the rest are aux relays (BPF, AUX).

Arrays: pick a preset in the Array menu (8 or 4 directions, a number of switching relays) or define your own. Each array remembers its own direction patterns and offset. Patterns are edited in Set.

Control: click a direction button or the compass, or turn the mouse wheel over the compass. ALL OFF switches every relay off. Demo mode talks to no hardware.

Frequency ranges: with CAT on, each range (kHz) can switch one aux relay (first match wins, all other aux relays go off outside any range). This is how a band-pass filter or frequency dependent feed is switched.

Transmit interlock: relays and directions are never switched while the rig transmits (also not by a remote client or by the frequency ranges). It uses the PTT state rigctld reports, so CAT must be enabled; an external PTT line is not seen. Optionally it also blocks when PTT cannot be read."""),

    ('CAT, Hamlib and Output', """Hamlib: the Hamlib menu opens a launcher for rigctld. It can download the latest Hamlib for Windows, list the supported radios, set COM port, baud rate, CI-V address and PTT type, and start/stop rigctld. Starting it points CAT at it automatically, and it can start by itself when the program starts.

CAT: the program polls rigctld (host/port/interval in Set) for frequency and PTT. The frequency and the rig's current mode (USB, LSB, CW, FM, PKTUSB...) are shown on the LED display; the frequency is also used for the frequency ranges and sent to the outputs.

Output: the frequency can be sent as a Kenwood style message (FA00014200000;, 8N1) to up to two COM ports, at a settable baud rate and interval (Output menu, needs pyserial). Typical use: an amplifier or other device that wants CAT."""),

    ('Remote: server and client', """Server and client use the same program (Remote menu). The client connects to the server's port (default 8765) and shows frequency, PTT, relays and direction live.

Security:
  All traffic is TLS encrypted. The server has a self-signed certificate; the client pins its SHA-256 fingerprint on first use and refuses to connect if it ever changes. Compare the fingerprint with the one shown on the server.
  Users live in users.json (salted scrypt hashes, passwords at least 10 characters). Failed logins are delayed and then lock out the address.
  Roles: viewer (display only), operator (can switch), admin (can switch and take control from another operator).
  Only one client controls at a time; others are refused until the controller has been idle 30 s.
  The transmit interlock is enforced on the server, so no client can bypass it.
  The relay board and rigctld are never exposed; only the server's TLS port is. A VPN or tunnel on top is still a good idea.

Command line (no window): --mode, --minimized, --cfg, --adduser, --role, --setpass, --deluser, --listusers, --gencert, --fingerprint, --setctlpass."""),

    ('WSJT-X / JTDX stream', """What it does: the server listens for the UDP stream of WSJT-X or JTDX, optionally copies it to up to 5 other targets, and passes it on to every client. Each client sends it out again as local UDP, so GridTracker, a logger or another WSJT-X on the client PC sees it as if the radio were local.

Setup:
  1. In WSJT-X/JTDX: Settings > Reporting > UDP Server = the 'listen on' address and port of the server (default 127.0.0.1:2237).
  2. Remote menu > WSJT-X / JTDX UDP stream: tick Enabled on the server and on the client.
  3. On the client set 'send to' to where the local program listens (default 127.0.0.1:2237).

All addresses can be unicast (e.g. 127.0.0.1) or multicast (224.x - 239.x). Multicast uses TTL 1 with loopback on. 'Also copy to' forwards the incoming stream to up to 5 other targets: programs on this PC or other PCs, unicast or multicast, each with its own address and port (not the listen port itself).

Messages are passed on unchanged, so every message type works. The latest Heartbeat/Status is remembered, so a client that connects mid-session is up to date at once. Garbage and oversized packets are ignored; a stalled client loses packets instead of filling memory.

Stream direction: server to client only. Answering back is a separate option (next topic)."""),

    ('WSJT-X / JTDX remote control', """What it does: lets the program on the client PC that receives the stream (WSJT-X, JTDX, GridTracker) answer to the WSJT-X/JTDX on the server PC: call a station (Reply), halt transmit, send free text, clear, replay, highlight a callsign.

How: the client sends the stream out from a fixed local UDP port. A program that answers to the source of what it receives lands on that port; the client sends the answer to the server over the TLS link, and the server delivers it to the real WSJT-X/JTDX. The server only answers to the address that WSJT-X/JTDX itself sends from.

Protection:
  Needs an operator or admin login AND the separate control password (min. 10 characters), set on the server (Remote menu > WSJT-X / JTDX remote control > Set..., or --setctlpass) and typed on the client. The password is stored as a salted hash.
  Wrong passwords count towards the login lockout; the client does not retry by itself.
  Only these message types pass: Reply, Halt Tx, Free text, Clear, Replay, Location, Highlight callsign. Close, Configure and Switch configuration are never passed.
  Same single-controller rule as the relays; Halt Tx always goes through. Rate limited.

Note: the client's program must answer to the source address of the packets it receives."""),

    ('PstRotator input', """What it does: a logger or rotator program that controls a PstRotator (UDP, default port 12000) can control the direction of this program instead. The azimuth it sends selects the closest direction of the active array (Array menu), taking the offset in Set into account (heading of a direction = its compass angle + offset). With two equally close directions the first one of the array wins.

Messages understood:
  <PST><AZIMUTH>123</AZIMUTH></PST>   switch to the direction closest to 123 degrees
  <PST>AZ?</PST>                      answered with AZ:123.0 (the current heading) to the sender, port 12001 (listen port + 1)
Everything else (elevation, stop, park...) is ignored. A direction that is already active is not switched again.

Setup: Set > PstRotator input: tick Enabled, choose the listen address and port, and point the sending program at that address and port. If PstRotator itself runs on the same PC it already uses port 12000; use another port or close it.

It works in every mode. In client mode the command is sent to the server like a click on a direction button, so the login role, the single-controller rule and the transmit interlock all apply. Everywhere the transmit interlock blocks switching while the rig transmits.

Security: UDP has no password. Keep the listen address on 127.0.0.1 unless the sender is on another PC; with 0.0.0.0 anyone on the network can switch the array."""),

    ('About', """Stationcontroller v{ver}

Controls via/with Hamlib, KMTronic relays and WSJT-X/JTDX.

Settings, users.json, the server certificate and the server log are saved next to the program.

73 ON4IQ"""),
]


# ──────────────────────────────────────────────────────────────────────────
# Main application
# ──────────────────────────────────────────────────────────────────────────
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.resizable(True, True)
        self.configure(bg='#f0f0f0')

        self.cfg = load_cfg()
        self.app_mode = FORCE_MODE or self.cfg.get('appMode', 'standalone')  # standalone | server | client
        self.ui_q = queue.Queue()      # callables from network threads, run on the UI thread
        self.users = UserStore()
        self.remote_server = None
        self.remote_client = None
        self.wsjt = None               # WsjtListener (server mode only)
        self.pst = None                # PstListener (PstRotator UDP input)
        self._pst_req = None           # (direction, time) of the last command we acted on
        self.pst_last = ''             # text of the last PstRotator command, for the Settings tab
        self._wsjt_sock = None         # client mode: socket used to re-emit the stream locally
        self.wsjt_out_count = 0
        self._wsjt_pw = ''              # client: control password typed this session
        self._remote_link_state = ''
        self._remote_detail = ''
        self._remote_role = None
        self._remote_ctl = None
        self._remote_clients = []
        self._cfg_view_seen = None
        self._title_shown = None
        self.active_dir = None
        self.relay_state = [False] * 8
        self.conn_ok = None  # None = not tried yet, True = last command succeeded, False = failed
        self.km = KMTronic(lambda: self.cfg, self.log_line)
        self.cat = CAT(lambda: self.cfg, self.log_line)
        self._busy = False
        self._pending = []            # commands clicked while another relay action was running
        self._off_requested = False   # ALL OFF was pressed: relays all off means 'no direction' (not a zero-pattern one)
        self._cat_busy = False
        self.freq_khz = None          # last frequency read from CAT, or None
        self.ptt = None               # True = transmitting, False = receiving, None = unknown
        self.rig_mode = None          # mode reported by the rig via CAT ('USB', 'CW'...), or None
        self._cat_active_aux = None   # which aux index the last matched range turned on
        self.amp_sers = [None, None]  # open serial ports (output 1, output 2), or None
        self._amp_busy = False
        self._amp_result = None       # worker -> UI hand-off, collected by _amp_tick
        self._amp_errs = [None, None] # last error per port, so a failing port doesn't spam the status bar
        self._amp_submenus = []
        self._amp_after = None        # pending after() id of the amplifier send timer

        self._build_ui()
        self._rebuild_dynamic_ui()  # populates matrix/dots/aux + their Settings rows from cfg
        self.protocol('WM_DELETE_WINDOW', self.on_close)
        self._remote_pump()
        if self.app_mode == 'client':
            # no hardware here: the server owns relays, CAT and the output ports
            for idx in (self._array_menu_idx, self._amp_menu_idx, self._hl_menu_idx):
                self.menubar.entryconfig(idx, state='disabled')
            self.remote_client = RemoteClient(self)
            self.remote_client.start()
        else:
            self._poll_status()
            self._cat_poll()
            self._amp_tick()
            if self.app_mode == 'server':
                self.remote_server = RemoteServer(self)
                try:
                    self.remote_server.start()
                except Exception as e:
                    self.toast(f'Server not started: {e}', err=True)
                self.wsjt = WsjtListener(self, self.remote_server.broadcast_wsjt)
                self.wsjt.start()
                self._remote_state_tick()
        self.pst_apply()
        self._update_title()
        if START_MIN or self.cfg.get('startMinimized'):
            self.after(200, self.iconify)

    # ── logging to the small status line ──
    def log_line(self, msg):
        print(msg)

    def _build_menu(self):
        # One size smaller than the default menu font, applied to every
        # Menu widget (menu bar + all dropdowns) created from here on.
        menu_font = ('Courier New', 8)
        self.option_add('*Menu.font', menu_font)

        self.menubar = tk.Menu(self, font=menu_font)

        # Order along the top: Control, View, Array, Settings.
        self.menubar.add_command(label='Run', command=lambda: self._show_tab('control'))
        self._run_menu_idx = self.menubar.index('end')  # stable index — label text changes later (● marker)

        view_menu = tk.Menu(self.menubar, tearoff=0, font=menu_font)
        # Independent on/off toggles rather than mutually-exclusive radio
        # choices, so any combination (e.g. matrix + aux, no compass) works.
        self.view_compass_var = tk.BooleanVar(value=True)
        self.view_matrix_var = tk.BooleanVar(value=True)
        self.view_aux_var = tk.BooleanVar(value=True)
        self.view_freq_var = tk.BooleanVar(value=True)
        view_menu.add_checkbutton(label='Compass', variable=self.view_compass_var,
                                   command=self._apply_view_mode)
        view_menu.add_checkbutton(label='Matrix', variable=self.view_matrix_var,
                                   command=self._apply_view_mode)
        view_menu.add_checkbutton(label='Aux Relays', variable=self.view_aux_var,
                                   command=self._apply_view_mode)
        view_menu.add_checkbutton(label='Frequency', variable=self.view_freq_var,
                                   command=self._apply_view_mode)
        self.menubar.add_cascade(label='View', menu=view_menu)

        self.array_menu = tk.Menu(self.menubar, tearoff=0, font=menu_font)
        self.array_preset_var = tk.StringVar(value=self.cfg.get('arrayPreset', '9ca'))
        self.menubar.add_cascade(label='Array', menu=self.array_menu)
        self._array_menu_idx = self.menubar.index('end')
        self._rebuild_array_menu()

        self.amp_enabled_var = tk.BooleanVar(value=bool(self.cfg.get('ampEnabled')))
        self.amp_port_var = tk.StringVar(value=self.cfg.get('ampPort', ''))
        self.amp_port2_var = tk.StringVar(value=self.cfg.get('ampPort2', ''))
        self.amp_baud_var = tk.IntVar(value=int(self.cfg.get('ampBaud', 9600)))
        self.amp_int_var = tk.IntVar(value=int(self.cfg.get('ampIntervalMs', 1000)))
        self.amp_menu = tk.Menu(self.menubar, tearoff=0, font=menu_font,
                                postcommand=self._rebuild_amp_menu)
        self.menubar.add_cascade(label='Output', menu=self.amp_menu)
        self._amp_menu_idx = self.menubar.index('end')
        self._rebuild_amp_menu()

        self.menubar.add_command(label='Hamlib', command=lambda: self._show_tab('hamlib'))
        self._hl_menu_idx = self.menubar.index('end')  # stable index — label text changes later (● marker)

        self.menubar.add_command(label='Remote', command=self._open_remote_dialog)

        self.menubar.add_command(label='Set', command=lambda: self._show_tab('settings'))
        self._set_menu_idx = self.menubar.index('end')  # stable index — label text changes later (● marker)

        info_menu = tk.Menu(self.menubar, tearoff=0, font=menu_font)
        for title, _text in INFO_TOPICS:
            info_menu.add_command(label=title, command=lambda t=title: self._show_info(t))
        self.menubar.add_cascade(label='Info', menu=info_menu)

        self.config(menu=self.menubar)

    def _rebuild_array_menu(self):
        """(Re)populate the Array menu: built-in presets, then any arrays
        the user has defined and saved, then the option to define a new
        one. Called at startup and again whenever a new array is saved."""
        self.array_menu.delete(0, 'end')
        for preset in ARRAY_PRESETS:
            self.array_menu.add_radiobutton(label=preset['label'], value=preset['key'],
                                             variable=self.array_preset_var,
                                             command=lambda p=preset: self._apply_array_preset(p))
        custom_arrays = self.cfg.get('customArrays', [])
        if custom_arrays:
            self.array_menu.add_separator()
            for preset in custom_arrays:
                self.array_menu.add_radiobutton(label=preset['label'], value=preset['key'],
                                                 variable=self.array_preset_var,
                                                 command=lambda p=preset: self._apply_array_preset(p))
        self.array_menu.add_separator()
        self.array_menu.add_command(label='Define new array…',
                                     command=self._open_define_array_dialog)

    # ── CAT output to up to two COM ports (Kenwood-style FA, 8N1, RS232) ──
    def _amp_ports(self):
        """Configured output ports as [(slot, device), ...] — slot 0/1, unused slots omitted."""
        return [(i, self.cfg.get(k, '')) for i, k in enumerate(('ampPort', 'ampPort2'))
                if self.cfg.get(k, '')]

    def _rebuild_amp_menu(self):
        """(Re)build the Output menu. Runs each time the menu opens so the COM
        port list is always current (USB adapters come and go)."""
        for m in self._amp_submenus:
            m.destroy()
        self._amp_submenus = []
        self.amp_menu.delete(0, 'end')
        menu_font = ('Courier New', 8)

        self.amp_menu.add_checkbutton(label='Output enabled', variable=self.amp_enabled_var,
                                      command=self._amp_toggle_enabled)
        self.amp_menu.add_separator()

        devices = [p.device for p in list_ports.comports()] if list_ports else []
        for slot, (key, var) in enumerate((('ampPort', self.amp_port_var),
                                           ('ampPort2', self.amp_port2_var))):
            cur = self.cfg.get(key, '')
            port_menu = tk.Menu(self.amp_menu, tearoff=0, font=menu_font)
            self._amp_submenus.append(port_menu)
            avail = list(devices)
            if cur and cur not in avail:
                avail.append(cur)  # keep a saved-but-unplugged port visible
            if not list_ports:
                port_menu.add_command(label='pyserial not installed', state='disabled')
            else:
                port_menu.add_radiobutton(label='(none)', value='', variable=var,
                                          command=lambda s_=slot: self._amp_choose_port(s_, ''))
                for dev in sorted(avail):
                    port_menu.add_radiobutton(label=dev, value=dev, variable=var,
                                              command=lambda s_=slot, d=dev: self._amp_choose_port(s_, d))
                if not devices:
                    port_menu.add_command(label='(no COM ports found)', state='disabled')
            self.amp_menu.add_cascade(label=f"Port {slot + 1}: {cur or '(none)'}", menu=port_menu)

        baud_menu = tk.Menu(self.amp_menu, tearoff=0, font=menu_font)
        self._amp_submenus.append(baud_menu)
        for b in AMP_BAUDS:
            baud_menu.add_radiobutton(label=str(b), value=b, variable=self.amp_baud_var,
                                      command=lambda bb=b: self._amp_set(ampBaud=bb))
        self.amp_menu.add_cascade(label=f"Baud rate: {self.cfg.get('ampBaud', 9600)}  (both ports)",
                                  menu=baud_menu)

        int_menu = tk.Menu(self.amp_menu, tearoff=0, font=menu_font)
        self._amp_submenus.append(int_menu)
        cur_int = int(self.cfg.get('ampIntervalMs', 1000))
        for ms in sorted(set(AMP_INTERVALS + [cur_int])):
            int_menu.add_radiobutton(label=f'{ms} ms', value=ms, variable=self.amp_int_var,
                                     command=lambda m=ms: self._amp_set(ampIntervalMs=m))
        int_menu.add_separator()
        int_menu.add_command(label='Custom...', command=self._amp_custom_interval)
        self.amp_menu.add_cascade(label=f'Update interval: {cur_int} ms', menu=int_menu)

        self.amp_menu.add_separator()
        self.amp_menu.add_command(label='Format: Kenwood FA, 8N1 (both ports)', state='disabled')

    def _amp_choose_port(self, slot, device):
        key, other_key = ('ampPort', 'ampPort2') if slot == 0 else ('ampPort2', 'ampPort')
        var = self.amp_port_var if slot == 0 else self.amp_port2_var
        if device and device == self.cfg.get(other_key, ''):
            var.set(self.cfg.get(key, ''))  # revert the radio selection
            self.toast(f'{device} is already used by Port {2 if slot == 0 else 1}', err=True)
            return
        self._amp_errs[slot] = None
        self._amp_set(**{key: device})
        # enabled but nothing left to send to -> switch the output off cleanly
        if self.cfg.get('ampEnabled') and not self._amp_ports():
            self.amp_enabled_var.set(False)
            self._amp_set(ampEnabled=False)

    def _amp_set(self, **kw):
        self.cfg.update(kw)
        save_cfg(self.cfg)
        self._amp_errs = [None, None]
        self._amp_update_label()
        # changed ports/baud are picked up by the next send (see _amp_send);
        # restart the timer now so a new interval applies immediately
        if self._amp_after is not None:
            self.after_cancel(self._amp_after)
        self._amp_after = self.after(20, self._amp_tick)

    def _amp_toggle_enabled(self):
        on = bool(self.amp_enabled_var.get())
        if on and serial is None:
            self.amp_enabled_var.set(False)
            messagebox.showerror('pyserial missing',
                                 'Output needs pyserial.\n\nInstall it with:\n    pip install pyserial')
            return
        if on and not self._amp_ports():
            self.amp_enabled_var.set(False)
            messagebox.showinfo('Choose a port', 'Pick at least one COM port first: Output \u2192 Port 1 / Port 2.')
            return
        self._amp_set(ampEnabled=on)
        self.toast('Output ' + ('ON' if on else 'OFF'))

    def _amp_custom_interval(self):
        ms = simpledialog.askinteger('Update interval', 'Milliseconds between frequency messages (50-60000):',
                                     parent=self, minvalue=50, maxvalue=60000,
                                     initialvalue=int(self.cfg.get('ampIntervalMs', 1000)))
        if ms:
            self.amp_int_var.set(ms)
            self._amp_set(ampIntervalMs=ms)

    @staticmethod
    def kenwood_fa(freq_khz):
        """Kenwood 'FA' answer: 11-digit frequency in Hz, ';' terminated."""
        return f"FA{int(round(freq_khz * 1000)):011d};"

    def _amp_update_label(self, text=None, error=False):
        if text is None:
            ports = self._amp_ports()
            if not self.cfg.get('ampEnabled'):
                text = 'OUT: off'
            else:
                text = f"OUT: {' + '.join(p for _, p in ports) or '?'} @ {self.cfg.get('ampBaud', 9600)} 8N1"
        self.amp_lbl.config(text=text, foreground='#cc0000' if error else '#666666')

    def _amp_close_all(self):
        for i, ser in enumerate(self.amp_sers):
            if ser is not None:
                try:
                    ser.close()
                except Exception:
                    pass
                self.amp_sers[i] = None

    def _amp_tick(self):
        interval = max(50, int(self.cfg.get('ampIntervalMs', 1000)))
        if self._amp_result is not None:
            res, self._amp_result = self._amp_result, None
            self._amp_done(*res)
        if self.cfg.get('ampEnabled'):
            if self.freq_khz is None:
                self._amp_update_label('OUT: waiting for CAT frequency')
            elif not self._amp_busy and self._amp_ports() and serial is not None:
                self._amp_send(self.freq_khz)
        elif any(s_ is not None for s_ in self.amp_sers) and not self._amp_busy:
            self._amp_close_all()  # switched off: release the COM ports
            self._amp_update_label()
        self._amp_after = self.after(interval, self._amp_tick)

    def _amp_send(self, freq_khz):
        msg = self.kenwood_fa(freq_khz)
        wanted = [self.cfg.get('ampPort', ''), self.cfg.get('ampPort2', '')]
        baud = int(self.cfg.get('ampBaud', 9600))
        self._amp_busy = True

        def worker():
            results = []  # (slot, device, error-or-None) — each port succeeds or fails on its own
            for slot, dev in enumerate(wanted):
                ser = self.amp_sers[slot]
                if not dev:  # slot unused (or just cleared): release a port that was open
                    if ser is not None:
                        try:
                            ser.close()
                        except Exception:
                            pass
                        self.amp_sers[slot] = None
                    continue
                err = None
                try:
                    if ser is not None and (not ser.is_open or ser.port != dev or ser.baudrate != baud):
                        try:
                            ser.close()
                        except Exception:
                            pass
                        ser = None
                    if ser is None:
                        ser = serial.Serial(dev, baud, bytesize=serial.EIGHTBITS, parity=serial.PARITY_NONE,
                                            stopbits=serial.STOPBITS_ONE, timeout=0, write_timeout=1)
                        self.amp_sers[slot] = ser
                    ser.write(msg.encode('ascii'))
                except Exception as e:
                    err = str(e)
                    try:
                        if self.amp_sers[slot] is not None:
                            self.amp_sers[slot].close()
                    except Exception:
                        pass
                    self.amp_sers[slot] = None
                results.append((slot, dev, err))
            self._amp_result = (msg, baud, results)  # picked up on the UI thread by _amp_tick

        threading.Thread(target=worker, daemon=True).start()

    def _amp_done(self, msg, baud, results):
        self._amp_busy = False
        lines, any_err = [msg], False
        for slot, dev, err in results:
            if err:
                any_err = True
                lines.append(f'{dev}: ERROR {err.splitlines()[0][:36]}')
                if err != self._amp_errs[slot]:  # report each distinct error once per port
                    self._amp_errs[slot] = err
                    self.toast(f'Output port {dev}: {err}', err=True)
            else:
                self._amp_errs[slot] = None
                lines.append(f'{dev}@{baud}: OK')
        self._amp_update_label('\n'.join(lines), error=any_err)

    # ── array presets ──
    def _apply_array_preset(self, preset):
        dirs = preset['dirs']
        switch = preset['switchRelays']
        self.cfg['arrayPreset'] = preset['key']
        self.cfg['arrayDirs'] = list(dirs)
        self.cfg['switchRelays'] = switch

        # Each preset remembers its own pattern edits (keyed by preset key)
        # so switching away and back restores what you last saved for it,
        # instead of silently reverting to the preset's factory defaults
        # every time it's reselected.
        saved = self.cfg['savedPatterns'].get(preset['key'])
        if saved and all(d in saved and len(saved[d]) == switch for d in dirs):
            source = saved
        else:
            source = preset['patterns']
            self.cfg['savedPatterns'][preset['key']] = dict(preset['patterns'])
        for d in dirs:
            self.cfg['dirPatterns'][d] = list(source[d])

        # Offset belongs to the array too, not a single global value — each
        # array keeps its own, defaulting to 0 the first time it's used.
        self.cfg['offset'] = self.cfg['savedOffsets'].get(preset['key'], 0)

        self._resize_aux_lists()
        save_cfg(self.cfg)
        self.active_dir = None
        self._rebuild_dynamic_ui()

    def _resize_aux_lists(self):
        """auxLabels/auxColors must have exactly (8 - switchRelays) entries."""
        n_aux = 8 - self.cfg['switchRelays']
        labels = self.cfg.get('auxLabels', [])
        colors = self.cfg.get('auxColors', [])
        self.cfg['auxLabels'] = [labels[i] if i < len(labels) else f'AUX {i+1}'
                                  for i in range(n_aux)]
        self.cfg['auxColors'] = [colors[i] if i < len(colors) else '#006600'
                                  for i in range(n_aux)]

    def _open_define_array_dialog(self):
        """Array → Define new array…: build a new array (which directions,
        how many switching relays) and save it permanently under a name so
        it shows up in the Array menu like any built-in preset from then on."""
        dlg = tk.Toplevel(self)
        dlg.title('Define new array')
        dlg.resizable(True, True)
        dlg.transient(self)
        sf = ScrollFrame(dlg, stretch=True)
        sf.pack(fill='both', expand=True)
        box = sf.inner

        ttk.Label(box, text='Name:', font=('Courier New', 9, 'bold')).grid(
            row=0, column=0, sticky='w', padx=8, pady=(8, 2))
        name_var = tk.StringVar()
        ttk.Entry(box, textvariable=name_var, width=28).grid(
            row=0, column=1, columnspan=3, sticky='w', padx=(0, 8), pady=(8, 2))

        ttk.Label(box, text='Directions used by this array:',
                  font=('Courier New', 9, 'bold')).grid(
            row=1, column=0, columnspan=4, sticky='w', padx=8, pady=(10, 2))
        dir_vars = {}
        for i, d in enumerate(DIRS):
            v = tk.BooleanVar(value=d in self.cfg.get('arrayDirs', DIRS))
            ttk.Checkbutton(box, text=d, variable=v).grid(
                row=2 + i // 4, column=i % 4, sticky='w', padx=8, pady=2)
            dir_vars[d] = v

        ttk.Label(box, text='Relays used for switching (0-8):',
                  font=('Courier New', 9, 'bold')).grid(
            row=4, column=0, columnspan=4, sticky='w', padx=8, pady=(10, 2))
        switch_var = tk.StringVar(value=str(self.cfg.get('switchRelays', 4)))
        ttk.Spinbox(box, from_=0, to=8, textvariable=switch_var, width=5).grid(
            row=5, column=0, sticky='w', padx=8, pady=(0, 2))
        ttk.Label(box, text='Remaining relays become aux relays. Pattern starts as\n'
                            'sequential binary per direction — edit it afterward in Settings.',
                  font=('Courier New', 7), foreground='#666666', justify='left').grid(
            row=6, column=0, columnspan=4, sticky='w', padx=8, pady=(0, 8))

        def on_ok():
            name = name_var.get().strip()
            if not name:
                messagebox.showerror('Invalid', 'Give the array a name.', parent=dlg)
                return
            chosen = [d for d in DIRS if dir_vars[d].get()]
            if not chosen:
                messagebox.showerror('Invalid', 'Pick at least one direction.', parent=dlg)
                return
            try:
                switch = int(switch_var.get())
            except ValueError:
                messagebox.showerror('Invalid', 'Switching relays must be a number.', parent=dlg)
                return
            if not (0 <= switch <= 8):
                messagebox.showerror('Invalid', 'Switching relays must be between 0 and 8.', parent=dlg)
                return

            # Unique key derived from the name, clashing with neither
            # built-in presets nor previously saved custom arrays.
            slug = ''.join(c if c.isalnum() else '_' for c in name.lower()).strip('_') or 'array'
            existing_keys = {p['key'] for p in ARRAY_PRESETS} | {p['key'] for p in self.cfg['customArrays']}
            key = f'custom_{slug}'
            n = 2
            while key in existing_keys:
                key = f'custom_{slug}_{n}'
                n += 1

            preset = {
                'key': key, 'label': name,
                'dirs': chosen, 'switchRelays': switch,
                'patterns': make_binary_patterns(chosen, switch),
            }
            self.cfg['customArrays'].append(preset)
            save_cfg(self.cfg)
            self._rebuild_array_menu()
            self.array_preset_var.set(key)
            dlg.destroy()
            self._apply_array_preset(preset)
            self.toast(f'Array "{name}" saved')

        btns = ttk.Frame(box)
        btns.grid(row=7, column=0, columnspan=4, pady=(0, 8))
        tk.Button(btns, text='Save', command=on_ok, width=8).pack(side='left', padx=4)
        tk.Button(btns, text='Cancel',
                  command=lambda: (self.array_preset_var.set(self.cfg['arrayPreset']), dlg.destroy()),
                  width=8).pack(side='left', padx=4)

    def _apply_view_mode(self):
        # Relay dots travel with the matrix (same info, same spot).
        (self.canvas.grid() if self.view_compass_var.get() else self.canvas.grid_remove())
        if self.view_matrix_var.get():
            self.matrix_frame.grid()
            self.dotrow.grid()
        else:
            self.matrix_frame.grid_remove()
            self.dotrow.grid_remove()
        (self.aux_frame.grid() if self.view_aux_var.get() else self.aux_frame.grid_remove())
        (self.freq_frame.grid() if self.view_freq_var.get() else self.freq_frame.grid_remove())
        self._shrink_to_fit()

    def _update_freq_display(self):
        theme = self.cfg['theme']
        self.freq_led.config(bg=theme['freqBg'])
        mode = f' {self.rig_mode}' if self.rig_mode else ''
        if self.freq_khz is not None and self.ptt:
            self.freq_led.config(text=f'{self.freq_khz/1000:9.5f} TX!{mode}', fg='#ff3030')  # transmitting
        elif self.freq_khz is not None:
            self.freq_led.config(text=f'{self.freq_khz/1000:9.5f} MHz{mode}', fg=theme['freqText'])
        elif self.cfg.get('catEnabled'):
            self.freq_led.config(text='--- NO CAT ---', fg='#cc3333')  # fixed red: error state
        else:
            self.freq_led.config(text='---.----- MHz', fg='#336633')  # fixed dim: disabled state

    def _shrink_to_fit(self):
        """Resize the window to the natural size of the visible tab. The tabs are ScrollFrames, so
        what does not fit on the screen is reached with scroll bars, and the user can still drag
        the window to any size afterwards."""
        self.minsize(1, 1)
        self.update_idletasks()
        self.update_idletasks()
        self.geometry('')
        self.update_idletasks()
        self.minsize(1, 1)

    # ── layout ──
    def _build_ui(self):
        self._build_menu()

        # A plain Frame swap instead of ttk.Notebook: a Notebook always sizes
        # itself to the LARGEST of all its tabs (even hidden ones), so the
        # window would stay oversized to fit Settings even while only the
        # smaller Control tab is shown and shrunk. With a manual swap, only
        # the currently-visible tab's frame is ever gridded, so the window's
        # natural size reflects just that one tab.
        # Control/Settings switching is driven from the menu bar itself (see
        # _build_menu) rather than a button row here.
        container = ttk.Frame(self)
        container.pack(fill='both', expand=True, padx=8, pady=8)
        container.rowconfigure(0, weight=1)
        container.columnconfigure(0, weight=1)
        # Every tab sits in a ScrollFrame: the window opens at the tab's natural size (capped to the
        # screen), can be resized freely, and scroll bars appear when the content does not fit.
        self.tab_main = ScrollFrame(container, center=True)
        self.tab_settings = ScrollFrame(container, stretch=True)
        self.tab_hamlib = ScrollFrame(container, stretch=True)
        self.settings_inner = self.tab_settings.inner

        self._build_main_tab(self.tab_main.inner)
        self._build_settings_tab(self.settings_inner)
        self.hamlib = HamlibPanel(self.tab_hamlib.inner, self)
        self.hamlib.pack(fill='both', expand=True)

        self.tab_main.grid(row=0, column=0, sticky='nsew')
        self._current_tab = 'control'
        self.menubar.entryconfig(self._run_menu_idx, label='● Run')

        # status / toast bar
        self.status_var = tk.StringVar(value='Ready')
        bar = ttk.Label(self, textvariable=self.status_var, anchor='w',
                         relief='sunken', padding=(6, 3))
        bar.pack(fill='x', side='bottom')

    def _show_tab(self, which):
        self._current_tab = which
        for t in (self.tab_main, self.tab_settings, self.tab_hamlib):
            t.grid_forget()
        if which == 'control':
            self.tab_main.grid(row=0, column=0, sticky='nsew')
        elif which == 'hamlib':
            self.tab_hamlib.grid(row=0, column=0, sticky='nsew')
        else:
            # 'nsew', not just 'n': Settings needs to actually stretch to
            # fill extra room when the window grows, so its scrollable
            # canvas can shrink the scrollbar's reach instead of staying
            # fixed at whatever size it was first shown at.
            self.tab_settings.grid(row=0, column=0, sticky='nsew')
        # Mark which one's active directly in its menu-bar label, since a
        # plain add_command entry has no built-in "pressed" state.
        for idx, key, name in ((self._run_menu_idx, 'control', 'Run'),
                               (self._hl_menu_idx, 'hamlib', 'Hamlib'),
                               (self._set_menu_idx, 'settings', 'Set')):
            self.menubar.entryconfig(idx, label=('● ' + name) if which == key else name)
        self._shrink_to_fit()

    def _build_main_tab(self, root):
        left = ttk.Frame(root)
        left.grid(row=0, column=0, sticky='n')

        # Compass canvas — gridded (not packed) so it can be shown/hidden
        # independently of the matrix below via the View menu, without
        # disturbing the vertical order of the other widgets.
        self.canvas = tk.Canvas(left, width=150, height=150, bg='white',
                                 highlightthickness=1, highlightbackground='#cccccc')
        self.canvas.grid(row=0, column=0)
        self.canvas.bind('<Button-1>', self._on_canvas_click)
        self.canvas._no_wheel_scroll = True  # the wheel steps through the directions here
        # Mouse wheel over the compass steps through the 8 directions.
        # Windows/Mac fire <MouseWheel> with event.delta; Linux fires
        # <Button-4>/<Button-5> instead — both are bound so it works
        # wherever the app runs.
        self.canvas.bind('<MouseWheel>', self._on_canvas_scroll)
        self.canvas.bind('<Button-4>', self._on_canvas_scroll)
        self.canvas.bind('<Button-5>', self._on_canvas_scroll)

        # 3x3 direction grid ("the matrix"), relay dots, and aux relays are
        # all rebuilt by _rebuild_dynamic_ui() whenever the active array
        # (directions / switching relay count) changes — here they're just
        # created empty and then filled by the first rebuild call.
        self.matrix_frame = ttk.Frame(left)
        self.matrix_frame.grid(row=1, column=0, pady=(10, 0))
        self.dotrow = ttk.Frame(left)
        self.dotrow.grid(row=2, column=0, pady=(8, 0))
        self.aux_frame = ttk.LabelFrame(left, text='AUX RELAYS')
        self.aux_frame.grid(row=3, column=0, pady=(10, 0))
        self.dir_buttons = {}
        self.relay_dots = []
        self.aux_buttons = []

        # Frequency "LED" readout — fed by CAT (Hamlib rigctld) polling.
        # Shown/hidden via View → Frequency.
        self.freq_frame = ttk.Frame(left)
        self.freq_frame.grid(row=4, column=0, pady=(10, 0))
        self.freq_led = tk.Label(self.freq_frame, text='---.----- MHz',
                                  bg='#001a00', fg='#33ff33',
                                  font=('Courier New', 13, 'bold'), width=21,  # fixed: a longer mode must not resize the window
                                  relief='sunken', bd=2, padx=8, pady=3)
        self.freq_led.pack()
        self.amp_lbl = ttk.Label(self.freq_frame, text='OUT: off', font=('Courier New', 7),
                                 foreground='#666666', justify='center')
        self.amp_lbl.pack(pady=(2, 0))

    def _rebuild_dynamic_ui(self):
        """(Re)build everything whose shape depends on the active array:
        the 3x3 matrix (only buttons for directions actually in the array),
        the relay indicator dots (one per switching relay), the aux relay
        buttons (one per remaining relay), and their matching rows in the
        Settings tab. Called once at startup and again every time the
        array preset changes."""
        arr_dirs = self.cfg['arrayDirs']
        n_switch = self.cfg['switchRelays']
        n_aux = 8 - n_switch

        # -- matrix --
        for w in self.matrix_frame.winfo_children():
            w.destroy()
        self.dir_buttons = {}
        layout = ['NW', 'N', 'NE', 'W', 'OFF', 'E', 'SW', 'S', 'SE']
        for idx, d in enumerate(layout):
            r, c = divmod(idx, 3)
            if d == 'OFF':
                self.off_btn = tk.Button(self.matrix_frame, text='ALL\nOFF', width=3, height=1,
                                          fg=self.cfg['offColor'], font=('Courier New', 6, 'bold'),
                                          command=self.all_off)
                self.off_btn.grid(row=r, column=c, padx=2, pady=2)
                continue
            if d not in arr_dirs:
                continue  # leave the cell empty — this direction isn't part of the array
            b = tk.Button(self.matrix_frame, text=d, width=3, height=1,
                          font=('Courier New', 9, 'bold'),
                          command=lambda dd=d: self.select_dir(dd))
            b.grid(row=r, column=c, padx=2, pady=2)
            self.dir_buttons[d] = b

        # -- relay dots: one per switching relay --
        for w in self.dotrow.winfo_children():
            w.destroy()
        self.relay_dots = []
        for i in range(n_switch):
            col = ttk.Frame(self.dotrow)
            col.grid(row=0, column=i, padx=2)
            dot = tk.Canvas(col, width=14, height=14, highlightthickness=0, bg='#f0f0f0')
            circle = dot.create_oval(1, 1, 13, 13, fill='#e0e0e0', outline='#cccccc')
            dot.pack()
            ttk.Label(col, text=f'R{i+1}', font=('Courier New', 6)).pack()
            self.relay_dots.append((dot, circle))

        # -- aux relays: whatever's left of the 8 --
        self.aux_frame.config(text=f'AUX RELAYS ({n_switch+1}–8)' if n_aux else 'AUX RELAYS (none)')
        for w in self.aux_frame.winfo_children():
            w.destroy()
        self.aux_buttons = []
        for i in range(n_aux):
            colf = ttk.Frame(self.aux_frame)
            colf.grid(row=i // 2, column=i % 2, padx=3, pady=3, sticky='ew')
            b = tk.Button(colf, text=self.cfg['auxLabels'][i], width=7,
                          font=('Courier New', 8, 'bold'),
                          command=lambda ii=i: self.toggle_aux(ii))
            b.pack()
            ttk.Label(colf, text=f'R{n_switch+i+1}', font=('Courier New', 7)).pack()
            self.aux_buttons.append(b)

        self._rebuild_settings_rows()
        self._apply_cfg_to_widgets()
        self._update_ui()
        self._shrink_to_fit()

    def _rebuild_settings_rows(self):
        """Rebuild the Settings tab's pattern matrix (rows=array directions,
        columns=switching relays) and aux label/color rows (one per aux
        relay) — their shape depends on the active array too."""
        arr_dirs = self.cfg['arrayDirs']
        n_switch = self.cfg['switchRelays']
        n_aux = 8 - n_switch

        for w in self.pat_frame.winfo_children():
            w.destroy()
        self.pat_frame.config(text=f'Direction → Relay (1-{n_switch}) pattern')
        ttk.Label(self.pat_frame, text='Dir', font=('Courier New', 8, 'bold')).grid(row=0, column=0)
        for i in range(n_switch):
            ttk.Label(self.pat_frame, text=f'R{i+1}', font=('Courier New', 8, 'bold')).grid(row=0, column=i + 1)
        ttk.Label(self.pat_frame, text='Color', font=('Courier New', 8, 'bold')).grid(row=0, column=n_switch + 1)
        self.pattern_vars = {}
        self.dir_color_vars = {}
        self.dir_color_swatches = {}
        for r, d in enumerate(arr_dirs, start=1):
            ttk.Label(self.pat_frame, text=d, font=('Courier New', 9, 'bold'), foreground='#0055cc').grid(
                row=r, column=0, padx=4, pady=2, sticky='w')
            varsN = []
            for i in range(n_switch):
                v = tk.BooleanVar()
                ttk.Checkbutton(self.pat_frame, variable=v).grid(row=r, column=i + 1, padx=4)
                varsN.append(v)
            self.pattern_vars[d] = varsN

            self.dir_color_vars[d] = tk.StringVar(value=self.cfg['dirColors'].get(d, '#0055cc'))
            swatch = tk.Button(self.pat_frame, width=3, relief='raised',
                                command=lambda dd=d: self._pick_dir_color(dd))
            swatch.grid(row=r, column=n_switch + 1, padx=4, pady=2)
            self.dir_color_swatches[d] = swatch

        for w in self.auxf_frame.winfo_children():
            w.destroy()
        if n_aux:
            self.freqf_frame.pack(fill='x', pady=(8, 0))
        else:
            self.freqf_frame.pack_forget()  # nothing to switch, so no ranges to set
        self.auxf_frame.config(text=f'Aux relays ({n_switch+1}-8): label and ON color' if n_aux
                                else 'Aux relays: none (all 8 relays used for switching)')
        self.aux_label_vars = []
        self.aux_color_vars = []
        self.aux_color_swatches = []
        for i in range(n_aux):
            ttk.Label(self.auxf_frame, text=f'R{n_switch+i+1}', font=('Courier New', 8, 'bold'),
                      foreground='#0055cc').grid(row=i, column=0, padx=4, pady=3, sticky='w')
            v = tk.StringVar()
            ttk.Entry(self.auxf_frame, textvariable=v, width=14).grid(row=i, column=1, padx=4, pady=3)
            self.aux_label_vars.append(v)

            cv = tk.StringVar(value=self.cfg['auxColors'][i])
            swatch = tk.Button(self.auxf_frame, width=3, relief='raised',
                                command=lambda ii=i: self._pick_aux_color(ii))
            swatch.grid(row=i, column=2, padx=4, pady=3)
            self.aux_color_vars.append(cv)
            self.aux_color_swatches.append(swatch)

    def _build_settings_tab(self, root):
        pad = {'padx': 6, 'pady': 4}

        # 3 rows x 2 columns: Connection + CAT (row 1), Direction pattern +
        # Aux relays (row 2), Colors spanning both columns (row 3).
        row1_left = ttk.Frame(root)
        row1_right = ttk.Frame(root)
        row2_left = ttk.Frame(root)
        row2_right = ttk.Frame(root)
        row3 = ttk.Frame(root)
        row1_left.grid(row=0, column=0, sticky='n', padx=4, pady=4)
        row1_right.grid(row=0, column=1, sticky='n', padx=4, pady=4)
        row2_left.grid(row=1, column=0, sticky='n', padx=4, pady=4)
        row2_right.grid(row=1, column=1, sticky='n', padx=4, pady=4)
        row3.grid(row=2, column=0, columnspan=2, sticky='ew', padx=4, pady=4)

        conn = ttk.LabelFrame(row1_left, text='Connection')
        conn.pack(fill='x')

        self.var_transport = tk.StringVar()
        self.var_host = tk.StringVar()
        self.var_port = tk.StringVar()
        self.var_user = tk.StringVar()
        self.var_pass = tk.StringVar()
        self.var_mode = tk.StringVar()
        self.var_demo = tk.BooleanVar()
        self.var_offset = tk.StringVar()

        def row(parent, r, label, widget):
            ttk.Label(parent, text=label, width=10).grid(row=r, column=0, sticky='w', **pad)
            widget.grid(row=r, column=1, sticky='ew', **pad)

        conn.columnconfigure(1, weight=1)
        transport_combo = ttk.Combobox(conn, textvariable=self.var_transport, state='readonly',
                                        values=['udp', 'http'])
        transport_combo.bind('<<ComboboxSelected>>', lambda e: self._update_transport_visibility())
        row(conn, 0, 'Transport', transport_combo)
        ttk.Label(conn, text='  udp = classic KMTronic UDP board (port 12345, no login)\n'
                              '  http = KMTronic WEB board (web interface, login)',
                  font=('Courier New', 7), foreground='#666666', justify='left').grid(
            row=1, column=0, columnspan=2, sticky='w', padx=6)
        row(conn, 2, 'Host / IP', ttk.Entry(conn, textvariable=self.var_host))
        row(conn, 3, 'Port', ttk.Entry(conn, textvariable=self.var_port))

        self.lbl_user = ttk.Label(conn, text='Username', width=10)
        self.ent_user = ttk.Entry(conn, textvariable=self.var_user)
        self.lbl_pass = ttk.Label(conn, text='Password', width=10)
        self.ent_pass = ttk.Entry(conn, textvariable=self.var_pass, show='*')
        self.lbl_user.grid(row=4, column=0, sticky='w', **pad)
        self.ent_user.grid(row=4, column=1, sticky='ew', **pad)
        self.lbl_pass.grid(row=5, column=0, sticky='w', **pad)
        self.ent_pass.grid(row=5, column=1, sticky='ew', **pad)

        self.lbl_mode = ttk.Label(conn, text='Mode', width=10)
        self.mode_combo = ttk.Combobox(conn, textvariable=self.var_mode, state='readonly',
                                        values=['ff', 'toggle'])
        self.lbl_mode.grid(row=6, column=0, sticky='w', **pad)
        self.mode_combo.grid(row=6, column=1, sticky='ew', **pad)
        self.lbl_mode_hint = ttk.Label(
            conn, text='  ff = /FF0101 direct on/off   ·   toggle = /relays.cgi?relay=N',
            font=('Courier New', 7), foreground='#666666')
        self.lbl_mode_hint.grid(row=7, column=0, columnspan=2, sticky='w', padx=6)

        ttk.Checkbutton(conn, text='Demo mode (no hardware)', variable=self.var_demo).grid(
            row=8, column=0, columnspan=2, sticky='w', padx=6, pady=(6, 2))
        row(conn, 9, 'Offset °', ttk.Entry(conn, textvariable=self.var_offset))
        self.var_beamwidth = tk.StringVar()
        row(conn, 10, 'Beam width °', ttk.Entry(conn, textvariable=self.var_beamwidth))
        ttk.Label(conn, text='  width of the shaded wedge behind the arrow',
                  font=('Courier New', 7), foreground='#666666').grid(
            row=11, column=0, columnspan=2, sticky='w', padx=6)

        # Direction pattern matrix + Aux labels/colors — contents are built
        # by _rebuild_settings_rows() since their shape (row/column count)
        # depends on the active array preset.
        self.pat_frame = ttk.LabelFrame(row2_left, text='Direction → Relay pattern')
        self.pat_frame.pack(fill='x')
        self.auxf_frame = ttk.LabelFrame(row2_right, text='Aux relays')
        self.auxf_frame.pack(fill='x')
        # Frequency → aux relay ranges live with the aux relays they switch (a separate
        # box, because auxf_frame's contents are rebuilt whenever the array changes).
        # The ranges only act while CAT is enabled and delivering a frequency.
        self.freqf_frame = ttk.LabelFrame(row2_right, text='Aux relays: frequency ranges (kHz)')
        self.freqf_frame.pack(fill='x', pady=(8, 0))
        ttk.Label(self.freqf_frame,
                  text='Rig frequency (CAT) \u2192 aux relay. First match wins; outside\n'
                       'any range, all aux relays switch off.',
                  font=('Courier New', 7), foreground='#666666', justify='left').grid(
            row=0, column=0, sticky='w', padx=6, pady=(4, 2))
        self.freqrange_rows_frame = ttk.Frame(self.freqf_frame)
        self.freqrange_rows_frame.grid(row=1, column=0, sticky='w', padx=6)
        self.freq_range_rows = []  # each: {'min': StringVar, 'max': StringVar, 'aux': StringVar, 'frame': Frame}
        tk.Button(self.freqf_frame, text='+ Add range', command=lambda: self._add_freq_range_row(),
                  font=('Courier New', 8)).grid(row=2, column=0, sticky='w', padx=6, pady=(4, 6))

        # Colors — ALL OFF button color + Theme, all in one wide box using
        # the full width of the Settings tab: several label+swatch pairs
        # per row instead of one long vertical list.
        colorsf = ttk.LabelFrame(row3, text='Colors')
        colorsf.pack(fill='x')
        color_items = [
            ('offColor', 'ALL OFF button'),
            ('appBg', 'App background'),
            ('canvasBg', 'Compass background'),
            ('ringColor', 'Compass ring'),
            ('wedgeColor', 'Shaded wedge'),
            ('matrixBg', 'Matrix idle background'),
            ('matrixText', 'Matrix idle text'),
            ('auxBg', 'Aux idle background'),
            ('auxText', 'Aux idle text'),
            ('freqBg', 'Frequency LED background'),
            ('freqText', 'Frequency LED text'),
        ]
        PER_ROW = 4  # label+swatch pairs per row — spreads the list across the full width
        self.theme_vars = {}
        self.theme_swatches = {}
        self.off_color_var = tk.StringVar(value=self.cfg['offColor'])
        self.off_color_swatch = None
        for idx, (key, label) in enumerate(color_items):
            r, c = divmod(idx, PER_ROW)
            ttk.Label(colorsf, text=label, font=('Courier New', 8)).grid(
                row=r, column=c * 2, padx=(8, 4), pady=4, sticky='w')
            if key == 'offColor':
                swatch = tk.Button(colorsf, width=3, relief='raised', command=self._pick_off_color)
                swatch.grid(row=r, column=c * 2 + 1, padx=(0, 8), pady=4, sticky='w')
                self.off_color_swatch = swatch
            else:
                v = tk.StringVar(value=self.cfg['theme'][key])
                swatch = tk.Button(colorsf, width=3, relief='raised',
                                    command=lambda k=key: self._pick_theme_color(k))
                swatch.grid(row=r, column=c * 2 + 1, padx=(0, 8), pady=4, sticky='w')
                self.theme_vars[key] = v
                self.theme_swatches[key] = swatch

        # CAT (Hamlib rigctld) — frequency-dependent aux switching.
        catf = ttk.LabelFrame(row1_right, text='CAT (Hamlib rigctld)')
        catf.pack(fill='x')

        self.var_cat_enabled = tk.BooleanVar()
        self.var_cat_host = tk.StringVar()
        self.var_cat_port = tk.StringVar()
        self.var_cat_poll = tk.StringVar()
        self.var_tx_interlock = tk.BooleanVar()
        self.var_tx_failclosed = tk.BooleanVar()

        ttk.Checkbutton(catf, text='Enabled', variable=self.var_cat_enabled).grid(
            row=0, column=0, columnspan=2, sticky='w', padx=6, pady=(4, 2))
        ttk.Label(catf, text='rigctld must be running (start it from the Hamlib menu).',
                  font=('Courier New', 7), foreground='#666666').grid(
            row=1, column=0, columnspan=4, sticky='w', padx=6)

        ttk.Label(catf, text='Host', width=8).grid(row=2, column=0, sticky='w', padx=6, pady=2)
        ttk.Entry(catf, textvariable=self.var_cat_host, width=14).grid(row=2, column=1, sticky='w', pady=2)
        ttk.Label(catf, text='Port', width=8).grid(row=2, column=2, sticky='w', padx=6, pady=2)
        ttk.Entry(catf, textvariable=self.var_cat_port, width=8).grid(row=2, column=3, sticky='w', pady=2)
        ttk.Label(catf, text='Poll (ms)', width=8).grid(row=3, column=0, sticky='w', padx=6, pady=2)
        ttk.Entry(catf, textvariable=self.var_cat_poll, width=8).grid(row=3, column=1, sticky='w', pady=2)
        ttk.Checkbutton(catf, text='Block relay / direction changes while transmitting',
                        variable=self.var_tx_interlock).grid(row=4, column=0, columnspan=4, sticky='w', padx=6, pady=(6, 0))
        ttk.Checkbutton(catf, text='...also block when PTT cannot be read',
                        variable=self.var_tx_failclosed).grid(row=5, column=0, columnspan=4, sticky='w', padx=6)
        ttk.Label(catf, text='Needs CAT enabled; uses the rig\'s PTT state as reported\nby rigctld (an external PTT line is not seen).',
                  font=('Courier New', 7), foreground='#666666', justify='left').grid(
            row=6, column=0, columnspan=4, sticky='w', padx=6, pady=(0, 6))

        pstf = ttk.LabelFrame(row1_right, text='PstRotator input (UDP)')
        pstf.pack(fill='x', pady=(8, 0))
        self.var_pst_enabled = tk.BooleanVar()
        self.var_pst_listen = tk.StringVar()
        self.var_pst_port = tk.StringVar()
        self.var_pst_reply = tk.BooleanVar()
        ttk.Checkbutton(pstf, text='Enabled: set the direction from PstRotator commands',
                        variable=self.var_pst_enabled).grid(row=0, column=0, columnspan=4, sticky='w', padx=6, pady=(4, 2))
        ttk.Label(pstf, text='Listen on', width=8).grid(row=1, column=0, sticky='w', padx=6, pady=2)
        ttk.Entry(pstf, textvariable=self.var_pst_listen, width=14).grid(row=1, column=1, sticky='w', pady=2)
        ttk.Label(pstf, text='Port', width=8).grid(row=1, column=2, sticky='w', padx=6, pady=2)
        ttk.Entry(pstf, textvariable=self.var_pst_port, width=8).grid(row=1, column=3, sticky='w', pady=2)
        ttk.Checkbutton(pstf, text='Answer AZ? queries (to port + 1)', variable=self.var_pst_reply).grid(
            row=2, column=0, columnspan=4, sticky='w', padx=6)
        ttk.Label(pstf, text='<PST><AZIMUTH>nnn</AZIMUTH></PST> selects the closest direction\n'
                             '(offset included). UDP has no password: keep 127.0.0.1\nunless the sender is on another PC.',
                  font=('Courier New', 7), foreground='#666666', justify='left').grid(
            row=3, column=0, columnspan=4, sticky='w', padx=6)
        self.lbl_pst = ttk.Label(pstf, text='', font=('Courier New', 7), justify='left')
        self.lbl_pst.grid(row=4, column=0, columnspan=4, sticky='w', padx=6, pady=(2, 6))

        apply_btn = tk.Button(root, text='Apply & Save', bg='#0055cc', fg='white',
                               font=('Courier New', 9, 'bold'), command=self.apply_settings)
        apply_btn.grid(row=3, column=0, columnspan=2, sticky='ew', padx=4, pady=10)
        root.columnconfigure(0, weight=1)
        root.columnconfigure(1, weight=1)

    # ── sync widgets from self.cfg ──
    def _apply_cfg_to_widgets(self):
        c = self.cfg
        self.var_transport.set(c.get('transport', 'udp'))
        self.var_host.set(c['host'])
        self.var_port.set(str(c['port']))
        self.var_user.set(c.get('user', 'admin'))
        self.var_pass.set(c.get('password', 'admin'))
        self.var_mode.set(c.get('mode', 'ff'))
        self.var_demo.set(bool(c['demo']))
        self.var_offset.set(str(c.get('offset', 0)))
        self.var_beamwidth.set(str(c.get('beamWidth', 45)))
        for d in c['arrayDirs']:
            pat = c['dirPatterns'].get(d, [0] * c['switchRelays'])
            for i, v in enumerate(self.pattern_vars[d]):
                v.set(bool(pat[i]) if i < len(pat) else False)
            color = c['dirColors'].get(d, '#0055cc')
            self.dir_color_vars[d].set(color)
            self.dir_color_swatches[d].config(bg=color)
        for i, v in enumerate(self.aux_label_vars):
            v.set(c['auxLabels'][i])
        for i in range(len(self.aux_color_vars)):
            color = c['auxColors'][i]
            self.aux_color_vars[i].set(color)
            self.aux_color_swatches[i].config(bg=color)
        self.off_color_var.set(c['offColor'])
        self.off_color_swatch.config(bg=c['offColor'])
        for key, v in self.theme_vars.items():
            color = c['theme'][key]
            v.set(color)
            self.theme_swatches[key].config(bg=color)
        self.var_cat_enabled.set(bool(c.get('catEnabled', False)))
        self.var_cat_host.set(c.get('catHost', '127.0.0.1'))
        self.var_cat_port.set(str(c.get('catPort', 4532)))
        self.var_cat_poll.set(str(c.get('catPollMs', 2000)))
        self.var_tx_interlock.set(bool(c.get('txInterlock', True)))
        self.var_tx_failclosed.set(bool(c.get('txInterlockFailClosed', False)))
        pc = c.get('pst', {})
        self.var_pst_enabled.set(bool(pc.get('enabled', False)))
        self.var_pst_listen.set(pc.get('listen', '127.0.0.1'))
        self.var_pst_port.set(str(pc.get('port', PST_PORT_DEFAULT)))
        self.var_pst_reply.set(bool(pc.get('reply', True)))
        self._pst_update_label()
        self._rebuild_freq_range_rows()
        self._update_badge()
        self._update_transport_visibility()

    def _pick_dir_color(self, d):
        current = self.dir_color_vars[d].get()
        _, hex_color = colorchooser.askcolor(color=current, title=f'Color for {d}')
        if hex_color:
            self.dir_color_vars[d].set(hex_color)
            self.dir_color_swatches[d].config(bg=hex_color)

    def _pick_aux_color(self, i):
        current = self.aux_color_vars[i].get()
        _, hex_color = colorchooser.askcolor(color=current, title=f'ON color for R{i+5}')
        if hex_color:
            self.aux_color_vars[i].set(hex_color)
            self.aux_color_swatches[i].config(bg=hex_color)

    def _pick_off_color(self):
        current = self.off_color_var.get()
        _, hex_color = colorchooser.askcolor(color=current, title='ALL OFF button color')
        if hex_color:
            self.off_color_var.set(hex_color)
            self.off_color_swatch.config(bg=hex_color)

    def _pick_theme_color(self, key):
        current = self.theme_vars[key].get()
        _, hex_color = colorchooser.askcolor(color=current, title=key)
        if hex_color:
            self.theme_vars[key].set(hex_color)
            self.theme_swatches[key].config(bg=hex_color)

    def _aux_options(self):
        """Combobox values for the frequency-range rows' aux picker: a
        '(none)' choice plus one entry per CURRENT aux relay, labelled with
        its current name."""
        return ['(none)'] + [f'{i+1}: {lbl}' for i, lbl in enumerate(self.cfg.get('auxLabels', []))]

    def _add_freq_range_row(self, min_khz='', max_khz='', aux_idx=None):
        row_frame = ttk.Frame(self.freqrange_rows_frame)
        row_frame.pack(fill='x', pady=2)

        min_var = tk.StringVar(value=str(min_khz))
        max_var = tk.StringVar(value=str(max_khz))
        options = self._aux_options()
        aux_label = options[aux_idx + 1] if (aux_idx is not None and 0 <= aux_idx + 1 < len(options)) else '(none)'
        aux_var = tk.StringVar(value=aux_label)

        ttk.Label(row_frame, text='Min', font=('Courier New', 7)).pack(side='left')
        ttk.Entry(row_frame, textvariable=min_var, width=9).pack(side='left', padx=(2, 6))
        ttk.Label(row_frame, text='Max', font=('Courier New', 7)).pack(side='left')
        ttk.Entry(row_frame, textvariable=max_var, width=9).pack(side='left', padx=(2, 6))
        ttk.Label(row_frame, text='→', font=('Courier New', 8)).pack(side='left', padx=(0, 4))
        aux_combo = ttk.Combobox(row_frame, textvariable=aux_var, state='readonly',
                                  values=options, width=14)
        aux_combo.pack(side='left', padx=(0, 6))
        entry = {'min': min_var, 'max': max_var, 'aux': aux_var, 'frame': row_frame}
        tk.Button(row_frame, text='✕', font=('Courier New', 7), fg='#cc0000', width=2,
                  command=lambda: self._remove_freq_range_row(entry)).pack(side='left')
        self.freq_range_rows.append(entry)
        self._shrink_to_fit()

    def _remove_freq_range_row(self, entry):
        entry['frame'].destroy()
        self.freq_range_rows.remove(entry)
        self._shrink_to_fit()

    def _rebuild_freq_range_rows(self):
        """Clear and recreate all rows from self.cfg['freqRanges'], with
        the aux picker's options refreshed to the CURRENT array's aux
        relay labels (counts/labels change when the array preset changes)."""
        for entry in list(self.freq_range_rows):
            entry['frame'].destroy()
        self.freq_range_rows = []
        for r in self.cfg.get('freqRanges', []):
            self._add_freq_range_row(r.get('min', ''), r.get('max', ''), r.get('aux'))

    def _update_transport_visibility(self):
        is_http = self.var_transport.get() == 'http'
        widgets = [self.lbl_user, self.ent_user, self.lbl_pass, self.ent_pass,
                   self.lbl_mode, self.mode_combo, self.lbl_mode_hint]
        for w in widgets:
            if is_http:
                w.grid()
            else:
                w.grid_remove()
        # sensible default port per transport, only if the user hasn't customised it
        if is_http and self.var_port.get() in ('', '12345'):
            self.var_port.set('80')
        elif not is_http and self.var_port.get() in ('', '80'):
            self.var_port.set('12345')

    def apply_settings(self):
        host = self.var_host.get().strip()
        try:
            port = int(self.var_port.get().strip())
        except ValueError:
            messagebox.showerror('Invalid', 'Port must be a number.')
            return
        try:
            offset = float(self.var_offset.get().strip() or 0)
        except ValueError:
            messagebox.showerror('Invalid', 'Offset must be a number.')
            return
        try:
            beam_width = float(self.var_beamwidth.get().strip() or 45)
        except ValueError:
            messagebox.showerror('Invalid', 'Beam width must be a number.')
            return
        if not host:
            messagebox.showerror('Invalid', 'Host / IP is required.')
            return
        if not (-180 <= offset <= 180):
            messagebox.showerror('Invalid', 'Offset must be between -180 and 180.')
            return
        if not (1 <= beam_width <= 90):
            messagebox.showerror('Invalid', 'Beam width must be between 1 and 90 degrees.')
            return

        try:
            cat_port = int(self.var_cat_port.get().strip())
            cat_poll_ms = int(self.var_cat_poll.get().strip())
        except ValueError:
            messagebox.showerror('Invalid', 'CAT port and poll interval must be numbers.')
            return
        if cat_poll_ms < 200:
            messagebox.showerror('Invalid', 'CAT poll interval must be at least 200 ms.')
            return

        try:
            pst_port = int(self.var_pst_port.get().strip())
            if not 1 <= pst_port <= 65535:
                raise ValueError
        except ValueError:
            messagebox.showerror('Invalid', 'PstRotator port must be a number between 1 and 65535.')
            return

        freq_ranges = []
        for entry in self.freq_range_rows:
            min_s, max_s = entry['min'].get().strip(), entry['max'].get().strip()
            if not min_s and not max_s:
                continue  # blank row, ignore
            try:
                min_v, max_v = float(min_s), float(max_s)
            except ValueError:
                messagebox.showerror('Invalid', 'Each frequency range needs numeric Min and Max (kHz).')
                return
            if min_v > max_v:
                messagebox.showerror('Invalid', 'A range\'s Min must not be greater than its Max.')
                return
            aux_choice = entry['aux'].get()
            aux_idx = None if aux_choice == '(none)' else int(aux_choice.split(':')[0]) - 1
            freq_ranges.append({'min': min_v, 'max': max_v, 'aux': aux_idx})

        # Start from copies of the existing patterns/colors (which may still
        # hold entries for directions outside the current array, e.g. from
        # a previous preset) and only overwrite the ones with live widgets.
        dir_patterns = dict(self.cfg.get('dirPatterns', {}))
        dir_colors = dict(self.cfg.get('dirColors', {}))
        for d in self.cfg['arrayDirs']:
            dir_patterns[d] = [1 if v.get() else 0 for v in self.pattern_vars[d]]
            dir_colors[d] = self.dir_color_vars[d].get()
        aux_labels = [v.get().strip() or f'AUX {i+1}' for i, v in enumerate(self.aux_label_vars)]

        # Remember this edit under the CURRENT array preset specifically, so
        # switching to a different array and back restores it rather than
        # reverting to that preset's factory-default pattern.
        saved_patterns = dict(self.cfg.get('savedPatterns', {}))
        saved_patterns[self.cfg['arrayPreset']] = {
            d: dir_patterns[d] for d in self.cfg['arrayDirs']
        }

        # Offset is per-array too, same as the pattern above.
        saved_offsets = dict(self.cfg.get('savedOffsets', {}))
        saved_offsets[self.cfg['arrayPreset']] = offset

        self.cfg = {
            **self.cfg,  # keep arrayPreset/arrayDirs/switchRelays as-is
            'transport': self.var_transport.get() or 'udp',
            'host': host, 'port': port,
            'user': self.var_user.get(), 'password': self.var_pass.get(),
            'mode': self.var_mode.get() or 'ff',
            'demo': bool(self.var_demo.get()),
            'offset': offset,
            'savedOffsets': saved_offsets,
            'beamWidth': beam_width,
            'dirPatterns': dir_patterns,
            'auxLabels': aux_labels,
            'dirColors': dir_colors,
            'auxColors': [v.get() for v in self.aux_color_vars],
            'offColor': self.off_color_var.get(),
            'theme': {k: v.get() for k, v in self.theme_vars.items()},
            'savedPatterns': saved_patterns,
            'catEnabled': bool(self.var_cat_enabled.get()),
            'catHost': self.var_cat_host.get().strip() or '127.0.0.1',
            'catPort': cat_port,
            'catPollMs': cat_poll_ms,
            'txInterlock': bool(self.var_tx_interlock.get()),
            'txInterlockFailClosed': bool(self.var_tx_failclosed.get()),
            'freqRanges': freq_ranges,
            'pst': {'enabled': bool(self.var_pst_enabled.get()),
                    'listen': self.var_pst_listen.get().strip() or '127.0.0.1',
                    'port': pst_port, 'reply': bool(self.var_pst_reply.get())},
        }
        save_cfg(self.cfg)
        self.conn_ok = None  # settings changed (host/transport/etc) — status unknown again
        self._cat_active_aux = None  # force re-evaluation against the (possibly changed) ranges
        self.pst_apply()
        for i, b in enumerate(self.aux_buttons):
            b.config(text=aux_labels[i])
        self._update_ui()
        self.toast(f"Settings saved (offset {'+' if offset >= 0 else ''}{offset:g}°)")

    def _update_badge(self):
        # Status is now shown as a dot on the compass (see _draw_compass),
        # not as text. Kept as a no-op so existing call sites don't need
        # removing; _update_ui() (called separately) redraws the dot.
        pass

    # ── background worker helper ──
    def _run_async(self, fn, on_done=None, queue=False):
        """Run fn in a worker thread, then on_done(result) on the UI thread. While another action
        runs: queue=True keeps the call and runs it right after (commands must not get lost),
        otherwise it is skipped. Returns False if the call was refused."""
        if self._busy:
            if queue and len(self._pending) < 6:
                self._pending.append((fn, on_done))
                return True
            return False
        self._busy = True

        def worker():
            try:
                result = fn()
            except Exception as e:
                # Never let an exception die silently in the background thread —
                # that used to leave the compass cleared (canvas.delete('all'))
                # with nothing redrawn, and the status text stuck from whatever
                # it was mid-update.
                import traceback
                traceback.print_exc()
                self.after(0, lambda: self._finish_async(None, on_done, error=str(e)))
                return
            self.after(0, lambda: self._finish_async(result, on_done))

        threading.Thread(target=worker, daemon=True).start()
        return True

    def _finish_async(self, result, on_done, error=None):
        self._busy = False
        if error:
            self.toast(f'Internal error: {error}', err=True)
        elif on_done:
            on_done(result)
        if self._pending and not self._busy:
            fn, od = self._pending.pop(0)
            self._run_async(fn, od)

    # ── transmit interlock ──
    # Relays/directions must never be switched while the rig is transmitting (hot
    # switching damages relays and can damage the antenna system). The check lives
    # here in the core, so it covers the local window, remote clients and the
    # automatic frequency->aux switching alike.
    TX_BLOCK_MSG = 'Blocked: radio is transmitting'

    def _tx_blocked_cached(self):
        """Fast check from the last CAT poll (UI thread). True = transmitting."""
        return bool(self.cfg.get('txInterlock', True) and self.cfg.get('catEnabled') and self.ptt)

    def _tx_guard(self):
        """Authoritative check, run in the worker thread right before relays are
        switched: asks rigctld for the PTT state *now* instead of trusting a poll
        that may be seconds old. Returns None if switching is allowed, otherwise
        the reason it is blocked."""
        if not self.cfg.get('txInterlock', True):
            return None
        if not self.cfg.get('catEnabled'):
            return None  # no CAT -> the interlock cannot know; see 'CAT off' note in the docs
        freq, ptt = self.cat.get_status()
        if ptt is not None:
            self.ptt = ptt
            if freq is not None:
                self.freq_khz = freq
        if ptt:
            return self.TX_BLOCK_MSG
        if ptt is None and self.cfg.get('txInterlockFailClosed'):
            return 'Blocked: radio PTT state unknown (CAT unreadable)'
        return None

    # ── actions ──
    def select_dir(self, d):
        if self.app_mode == 'client':
            return self._remote_cmd('select_dir', dir=d)
        self.toast(f'Switching to {d}…')

        def work():
            blocked = self._tx_guard()
            if blocked:
                return blocked
            pattern = self.cfg['dirPatterns'][d]
            for i, want in enumerate(pattern):
                if not self.km.send_relay(i + 1, want == 1, self.relay_state):
                    return False
            return True

        def done(ok):
            if isinstance(ok, str):  # interlock refused the change
                self._update_ui()
                self.toast(ok, err=True)
                return
            self.conn_ok = ok
            if ok:
                self.active_dir = d
                self._off_requested = False
                self._update_ui()
                tb = (ANGLES[d] + self.cfg.get('offset', 0)) % 360
                self.toast(f'▶ {d}  ·  {tb:.0f}° true')
            else:
                self._update_ui()  # redraw so the status dot reflects the failure
                self.toast('Connection failed — check settings', err=True)

        if not self._run_async(work, done, queue=True):
            self.toast('Busy, try again', err=True)

    def toggle_aux(self, idx):
        if self.app_mode == 'client':
            return self._remote_cmd('toggle_aux', idx=idx)
        relay_num = idx + self.cfg['switchRelays'] + 1
        new_state = not self.relay_state[relay_num - 1]

        def work():
            blocked = self._tx_guard()
            if blocked:
                return blocked
            return self.km.send_relay(relay_num, new_state, self.relay_state)

        def done(ok):
            if isinstance(ok, str):
                self._update_ui()
                self.toast(ok, err=True)
                return
            self.conn_ok = ok
            if ok:
                self._update_ui()
                label = self.cfg['auxLabels'][idx]
                self.toast(f"{label}  →  {'ON' if new_state else 'OFF'}")
            else:
                self._update_ui()
                self.toast('Connection failed', err=True)

        if not self._run_async(work, done, queue=True):
            self.toast('Busy, try again', err=True)

    def all_off(self):
        if self.app_mode == 'client':
            return self._remote_cmd('all_off')
        self.toast('Turning all relays off…')
        self.off_btn.config(bg=self.cfg['offColor'], fg='white', relief='sunken')

        def work():
            blocked = self._tx_guard()
            if blocked:
                return blocked
            return self.km.all_off(self.relay_state)

        def done(ok):
            self.off_btn.config(bg='#f0f0f0', fg=self.cfg['offColor'], relief='raised')
            if isinstance(ok, str):
                self._update_ui()
                self.toast(ok, err=True)
                return
            self.conn_ok = ok
            if ok:
                self.active_dir = None
                self._off_requested = True  # relays all off now means 'no direction'
                self._update_ui()
                self.toast('All relays OFF')
            else:
                self._update_ui()
                self.toast('Connection failed — check IP / network', err=True)

        if not self._run_async(work, done, queue=True):
            self.off_btn.config(bg='#f0f0f0', fg=self.cfg['offColor'], relief='raised')
            self.toast('Busy, try again', err=True)

    def _on_canvas_click(self, event):
        cx, cy = 75, 75
        dx, dy = event.x - cx, event.y - cy
        if math.hypot(dx, dy) < 10:
            return
        angle = math.degrees(math.atan2(dy, dx)) + 90
        if angle < 0:
            angle += 360
        snap = round(angle / 45) * 45 % 360
        for d, a in ANGLES.items():
            if a == snap and d in self.cfg['arrayDirs']:
                self.select_dir(d)
                break
            # a direction not in the active array is simply not clickable

    def _on_canvas_scroll(self, event):
        if self._busy:
            return  # a command is still in flight — don't queue another
        arr_dirs = self.cfg['arrayDirs']
        # Linux sends Button-4 (up) / Button-5 (down) with no delta;
        # Windows/Mac send MouseWheel with event.delta (+120 / -120 per notch).
        if getattr(event, 'num', None) in (4, 5):
            step = 1 if event.num == 4 else -1
        else:
            step = 1 if event.delta > 0 else -1
        idx = arr_dirs.index(self.active_dir) if self.active_dir in arr_dirs else -1
        self.select_dir(arr_dirs[(idx + step) % len(arr_dirs)])

    # ── background status polling ──
    def _direction_for_relays(self, cur):
        """The direction the switching relays (bits in cur, e.g. '1100') are set to, or None.
        The compass always follows the relays, also when they were changed outside this program
        or the board was reset. One case is ambiguous: all relays off can be 'no direction' or a
        direction whose own pattern is all zero (NE on the 9CA). It is read as 'no direction'
        only after the user pressed ALL OFF; otherwise as that direction, because that is what
        the relays physically are."""
        matches = [d for d in self.cfg['arrayDirs']
                   if ''.join(str(x) for x in self.cfg['dirPatterns'].get(d, [])) == cur]
        if '1' not in cur and self._off_requested:
            return None
        if self.active_dir in matches:
            return self.active_dir
        return matches[0] if matches else None

    def _poll_status(self):
        def work():
            return self.km.read_status()

        def done(st):
            if st:
                self.conn_ok = True  # a successful status read confirms the board is reachable
                self.relay_state = st
                n_switch = self.cfg['switchRelays']
                if n_switch:
                    cur = ''.join('1' if v else '0' for v in st[:n_switch])
                    if '1' in cur:
                        self._off_requested = False
                    self.active_dir = self._direction_for_relays(cur)
                self._update_ui()

        if not self._busy and not self.cfg.get('demo'):
            self._run_async(work, done)
        self.after(1500, self._poll_status)

    # ── CAT (Hamlib rigctld) polling for frequency-dependent aux switching ──
    def _cat_poll(self):
        if self._cat_busy or not self.cfg.get('catEnabled'):
            self.after(self.cfg.get('catPollMs', 2000), self._cat_poll)
            return
        self._cat_busy = True

        def worker():
            freq, ptt, mode = self.cat.get_status_full()
            self.after(0, lambda: self._cat_poll_done(freq, ptt, mode))

        threading.Thread(target=worker, daemon=True).start()

    def _cat_poll_done(self, freq_khz, ptt=None, mode=None):
        self._cat_busy = False
        self.freq_khz = freq_khz
        self.ptt = ptt
        self.rig_mode = mode if freq_khz is not None else None
        self._update_freq_display()
        # While transmitting, leave the aux relays alone: _cat_active_aux is not updated,
        # so the switch is simply made on the first poll after the rig is back on receive.
        if freq_khz is not None and not self._busy and not self._tx_blocked_cached():
            matched = CAT.find_range(freq_khz, self.cfg.get('freqRanges', []))
            target_aux = matched['aux'] if matched else None
            if target_aux != self._cat_active_aux:
                self._cat_active_aux = target_aux
                self._apply_freq_aux(target_aux)
        self.after(self.cfg.get('catPollMs', 2000), self._cat_poll)

    def _apply_freq_aux(self, target_aux):
        """Switch ON the aux relay matching the current frequency range (if
        any) and OFF every other aux relay — a mutually-exclusive bank,
        matching how a BPF switch or frequency-dependent array feed usually
        works. target_aux is an index into the CURRENT array's aux relays,
        or None to just switch all aux relays off."""
        n_switch = self.cfg['switchRelays']
        n_aux = 8 - n_switch

        def work():
            blocked = self._tx_guard()
            if blocked:
                return blocked
            ok_all = True
            for i in range(n_aux):
                want_on = (i == target_aux)
                if not self.km.send_relay(n_switch + i + 1, want_on, self.relay_state):
                    ok_all = False
            return ok_all

        def done(ok):
            if isinstance(ok, str):
                self._cat_active_aux = None  # not switched: retry on the next poll
                self._update_ui()
                self.toast('CAT: aux change postponed \u2014 ' + ok.lower().replace('blocked: ', ''), err=True)
                return
            self.conn_ok = ok
            self._update_ui()
            if ok and target_aux is not None:
                label = self.cfg['auxLabels'][target_aux] if target_aux < len(self.cfg['auxLabels']) else f'AUX {target_aux+1}'
                self.toast(f'CAT: {self.freq_khz/1000:.4f} MHz → {label}')
            elif ok:
                self.toast(f'CAT: {self.freq_khz/1000:.4f} MHz → no matching range, aux off')
            else:
                self.toast('CAT: frequency range matched but relay command failed', err=True)

        self._run_async(work, done)

    # ── UI refresh ──
    def _update_ui(self):
        theme = self.cfg['theme']
        self.configure(bg=theme['appBg'])
        self.canvas.config(bg=theme['canvasBg'])

        # Idle ALL OFF text color (its bg/fg flip to red/white only while a
        # command is actually in flight, handled separately in all_off()).
        self.off_btn.config(fg=self.cfg['offColor'])

        self._update_freq_display()

        for d, b in self.dir_buttons.items():
            if d == self.active_dir:
                # relief + text marker, not just color: on some platforms
                # (notably macOS) native buttons ignore bg/fg entirely, which
                # would otherwise make the selected label invisible.
                color = self.cfg['dirColors'].get(d, DEFAULT_DIR_COLORS[d])
                b.config(bg=color, fg='white', relief='sunken', text=f'▶{d}')
            else:
                b.config(bg=theme['matrixBg'], fg=theme['matrixText'], relief='raised', text=d)

        for i, (dot, circle) in enumerate(self.relay_dots):
            on = self.relay_state[i]
            dot.itemconfig(circle, fill='#0055cc' if on else '#e0e0e0',
                            outline='#0055cc' if on else '#cccccc')

        for i, b in enumerate(self.aux_buttons):
            on = self.relay_state[i + self.cfg['switchRelays']]
            on_color = self.cfg['auxColors'][i]
            b.config(bg=on_color if on else theme['auxBg'],
                     fg='white' if on else theme['auxText'])

        self._draw_compass()

    @staticmethod
    def _lighten(hex_color, amount=0.82):
        """Blend a hex color toward white for the compass wedge fill."""
        hex_color = hex_color.lstrip('#')
        try:
            r0, g0, b0 = (int(hex_color[i:i + 2], 16) for i in (0, 2, 4))
        except ValueError:
            return '#dbe8fa'
        r1 = int(r0 + (255 - r0) * amount)
        g1 = int(g0 + (255 - g0) * amount)
        b1 = int(b0 + (255 - b0) * amount)
        return f'#{r1:02x}{g1:02x}{b1:02x}'

    def _draw_compass(self):
        c = self.canvas
        c.delete('all')
        cx, cy, r = 75, 75, 64
        off = self.cfg.get('offset', 0)
        theme = self.cfg['theme']

        c.create_text(4, 4, text=f'v{APP_VERSION}', anchor='nw',
                      fill='#999999', font=('Courier New', 6))
        active_color = (self.cfg['dirColors'].get(self.active_dir, DEFAULT_DIR_COLORS.get(self.active_dir, '#0055cc'))
                         if self.active_dir else '#0055cc')

        def label_xy(deg, radius):
            a = math.radians(deg - 90)
            return cx + radius * math.cos(a), cy + radius * math.sin(a)

        if self.active_dir:
            a = math.radians(ANGLES[self.active_dir] + off - 90)
            half = math.radians(self.cfg.get('beamWidth', 45) / 2)
            pts = [cx, cy]
            steps = 12
            for i in range(steps + 1):
                ang = a - half + (2 * half) * i / steps
                pts += [cx + (r - 2) * math.cos(ang), cy + (r - 2) * math.sin(ang)]
            c.create_polygon(pts, fill=theme['wedgeColor'], outline='')

        c.create_oval(cx - r, cy - r, cx + r, cy + r, outline=theme['ringColor'])

        c.create_oval(cx - 4, cy - 4, cx + 4, cy + 4, fill=active_color, outline='')

        # Arrow is drawn BEFORE the direction labels, so the labels (N/NE/E/...)
        # always stay on top and never get painted over by the arrowhead,
        # which otherwise happens for the diagonal (2-letter) directions.
        if self.active_dir:
            a = math.radians(ANGLES[self.active_dir] + off - 90)
            arrow_len = r - 14   # stays inside the ring, well clear of the edge
            ex, ey = cx + arrow_len * math.cos(a), cy + arrow_len * math.sin(a)
            c.create_line(cx, cy, ex, ey, fill=active_color, width=3)
            hl, hw = 10, 5
            bx, by = ex - hl * math.cos(a), ey - hl * math.sin(a)
            p1 = (bx + hw * math.cos(a + math.pi / 2), by + hw * math.sin(a + math.pi / 2))
            p2 = (bx - hw * math.cos(a + math.pi / 2), by - hw * math.sin(a + math.pi / 2))
            c.create_polygon(ex, ey, *p1, *p2, fill=active_color, outline='')

        for d in self.cfg['arrayDirs']:  # only show ticks/labels for directions the array actually uses
            active = d == self.active_dir
            dcolor = self.cfg['dirColors'].get(d, DEFAULT_DIR_COLORS[d])
            x1, y1 = label_xy(ANGLES[d], r - 3)
            x2, y2 = label_xy(ANGLES[d], r - 10)
            c.create_line(x1, y1, x2, y2, fill=dcolor if active else '#cccccc',
                          width=2 if active else 1)
            lx, ly = label_xy(ANGLES[d], r - 20)
            c.create_text(lx, ly, text=d, fill=dcolor if active else '#888888',
                          font=('Courier New', 9, 'bold' if len(d) == 1 else 'normal'))

        if off:
            c.create_text(cx, cy + r - 6, text=f"offset {'+' if off >= 0 else ''}{off:g}°",
                          fill='#aaaaaa', font=('Courier New', 8))

        # Connection status dot, top-right corner of the canvas:
        #   gray   = demo mode (not actually talking to hardware)
        #   green  = live, and the last command/status read succeeded
        #   red    = live, and the last command/status read failed
        #   orange = live, but nothing sent/read yet (unknown)
        is_demo = self.cfg.get('demo', True)
        if is_demo:
            dot_color = '#888888'
        elif self.conn_ok is True:
            dot_color = '#009900'
        elif self.conn_ok is False:
            dot_color = '#cc0000'
        else:
            dot_color = '#cc8800'
        dot_x, dot_y, dot_r = 140, 10, 5
        c.create_oval(dot_x - dot_r, dot_y - dot_r, dot_x + dot_r, dot_y + dot_r,
                      fill=dot_color, outline='#666666')

    # ── remote operation: shared ──
    def _remote_pump(self):
        """Runs what the network threads queued up (never touch Tk from those threads)."""
        try:
            while True:
                fn = self.ui_q.get_nowait()
                try:
                    fn()
                except Exception:
                    import traceback
                    traceback.print_exc()  # one failing callback must not stop the pump
        except queue.Empty:
            pass
        self.after(50, self._remote_pump)

    def _show_info(self, topic):
        """Info menu: show one topic in a small read-only window (reused between topics)."""
        text = next((t for n, t in INFO_TOPICS if n == topic), '').replace('{ver}', APP_VERSION)
        win = getattr(self, '_info_win', None)
        if win is None or not win.winfo_exists():
            win = tk.Toplevel(self)
            win.geometry('680x520')
            frame = ttk.Frame(win)
            frame.pack(fill='both', expand=True)
            box = tk.Text(frame, wrap='word', font=('Courier New', 9), padx=10, pady=8, state='disabled')
            sb = ttk.Scrollbar(frame, orient='vertical', command=box.yview)
            box.config(yscrollcommand=sb.set)
            sb.pack(side='right', fill='y')
            box.pack(side='left', fill='both', expand=True)
            win._box = box
            self._info_win = win
        win.title(f'Stationcontroller - Info: {topic}')
        win._box.config(state='normal')
        win._box.delete('1.0', 'end')
        win._box.insert('1.0', text)
        win._box.config(state='disabled')
        win.lift()
        win.focus_set()

    def _open_remote_dialog(self):
        RemoteDialog(self)

    def _update_title(self):
        t = APP_TITLE
        if self.app_mode == 'server':
            n = len(self._remote_clients)
            t += ' \u00b7 SERVER'
            if self.remote_server and self.remote_server.error:
                t += ' (NOT LISTENING)'
            elif n:
                t += f" ({n} client{'s' if n != 1 else ''}: {', '.join(self._remote_clients)})"
        elif self.app_mode == 'client':
            rc = self.cfg.get('remote', {})
            who = f"{rc.get('cUser', '')}@{rc.get('cHost', '')}"
            st = self._remote_link_state
            if st == 'connected':
                ctl = f" \u00b7 control: {self._remote_ctl}" if self._remote_ctl else ''
                t += f' \u00b7 REMOTE {who} ({self._remote_role}){ctl}'
            else:
                t += ' \u00b7 REMOTE ' + {'connecting': 'CONNECTING...', 'disconnected': 'DISCONNECTED, retrying',
                                          'auth-failed': 'LOGIN REFUSED', 'cert-mismatch': 'SERVER CERTIFICATE CHANGED',
                                          '': 'starting...'}.get(st, st)
        if t != self._title_shown:
            self._title_shown = t
            self.title(t)

    # ── remote operation: server side ──
    def _remote_state(self):
        return {'freq': self.freq_khz, 'ptt': self.ptt, 'mode': self.rig_mode, 'relays': list(self.relay_state),
                'dir': self.active_dir, 'conn': self.conn_ok}

    def _remote_cfg_view(self):
        return {k: self.cfg[k] for k in CFG_VIEW_KEYS if k in self.cfg}

    def _remote_state_tick(self):
        srv = self.remote_server
        if srv and srv.running:
            self._remote_clients = srv.push_state(self._remote_state(), self._remote_cfg_view())
        self._update_title()
        self.after(400, self._remote_state_tick)

    # ── remote operation: client side ──
    def _remote_cmd(self, cmd, **args):
        rc = self.remote_client
        if not rc or rc.state != 'connected':
            self.toast('Not connected to the server', err=True)
            return
        if self._remote_role == 'viewer':
            self.toast('View-only account', err=True)
            return
        rc.send_cmd(cmd, **args)

    def _remote_link(self, state, detail=''):
        self._remote_link_state, self._remote_detail = state, detail
        if state == 'connected':
            self.toast('Connected to the server')
        else:
            # whatever was last shown is no longer live: don't let it look current
            self.conn_ok, self.freq_khz, self.ptt, self.rig_mode = False, None, None, None
            self._update_ui()
            if state == 'disconnected':
                self.toast(f'Disconnected from the server: {detail}' if detail else 'Disconnected from the server', err=True)
            elif state == 'auth-failed':
                messagebox.showerror('Login refused', f'The server refused the login: {detail}\n\n'
                                     'Check user name and password in Remote settings. Automatic retries stopped.')
            elif state == 'cert-mismatch':
                fp = fmt_fingerprint(detail) if len(detail) == 64 else detail
                messagebox.showerror(
                    'Server identity changed',
                    'The server\'s certificate does not match the one pinned on this PC.\n\n'
                    f'Presented: {fp}\n\n'
                    'This can mean someone is intercepting the connection. If the server\'s '
                    'certificate was regenerated on purpose, clear the pinned fingerprint in '
                    'Remote settings and verify the new one with the server operator.\n\n'
                    'The connection was refused.')
        self._update_title()

    def _remote_set_role(self, role):
        self._remote_role = role
        if role == 'viewer':
            self.toast('Connected: view-only account')
        self._update_title()

    def _remote_apply_cfg(self, view):
        for k in CFG_VIEW_KEYS:
            if k not in view:
                continue
            if k in ('dirPatterns', 'dirColors'):
                self.cfg[k] = {**self.cfg.get(k, {}), **view[k]}  # keep our own colours for unused directions
            else:
                self.cfg[k] = view[k]
        self.array_preset_var.set(self.cfg.get('arrayPreset', ''))
        self._resize_aux_lists()
        self._rebuild_dynamic_ui()

    def _remote_apply_state(self, st):
        if 'cfg' in st:
            self._remote_apply_cfg(st['cfg'])
        relays = st.get('relays')
        if isinstance(relays, list) and len(relays) == 8:
            self.relay_state = [bool(x) for x in relays]
        self.active_dir = st.get('dir')
        self.freq_khz = st.get('freq')
        self.ptt = st.get('ptt')
        self.rig_mode = st.get('mode')
        self.conn_ok = st.get('conn')
        self._remote_ctl = st.get('ctl')
        self._update_ui()
        self._update_title()

    # ── PstRotator input ──
    def pst_apply(self):
        """(Re)start the PstRotator listener from the current settings."""
        if self.pst is None:
            self.pst = PstListener(self)
        self.pst.start()
        self._pst_update_label()

    def _pst_update_label(self):
        lbl = getattr(self, 'lbl_pst', None)
        p = self.pst
        if lbl is None or p is None:
            return
        if p.listening:
            txt, col = f'Listening on {p.listening}', '#008000'
        elif p.error:
            txt, col = f'Not listening: {p.error}', '#cc0000'
        else:
            txt, col = 'Off', '#666666'
        if self.pst_last:
            txt += f'\nLast: {self.pst_last}'
        lbl.config(text=txt, foreground=col)

    def _closest_direction(self, az):
        """(difference in degrees, direction) of the array direction closest to azimuth az.
        A direction's heading is its compass angle plus the offset; ties go to the first one."""
        off = self.cfg.get('offset', 0)
        best = None
        for d in self.cfg.get('arrayDirs', []):
            diff = abs((az - (ANGLES[d] + off) + 180) % 360 - 180)
            if best is None or diff < best[0] - 1e-9:
                best = (diff, d)
        return best

    def _pst_command(self, kind, val, addr):
        """UI thread: one parsed PstRotator command."""
        pc = self.cfg.get('pst', {})
        if not pc.get('enabled'):
            return
        if kind == 'query':
            p = self.pst
            if pc.get('reply', True) and p and p.sock and self.active_dir in ANGLES:
                hdg = (ANGLES[self.active_dir] + self.cfg.get('offset', 0)) % 360
                try:
                    p.sock.sendto(f'AZ:{hdg:.1f}\r\n'.encode('ascii'),
                                  (addr[0], int(pc.get('port', PST_PORT_DEFAULT)) + 1))
                except OSError:
                    pass
            return
        best = self._closest_direction(val)
        if best is None:
            return
        diff, d = best
        self.pst_last = f'{val:.0f}\u00b0 \u2192 {d}' + (f' ({diff:.0f}\u00b0 off)' if diff >= 1 else '')
        self._pst_update_label()
        now = time.time()
        if d == self.active_dir:
            return                          # already there
        if self._pst_req and self._pst_req[0] == d and now - self._pst_req[1] < 3.0:
            return                          # the same command repeated while it is being carried out
        self._pst_req = (d, now)
        self.toast(f'PstRotator: {val:.0f}\u00b0 \u2192 {d}')
        self.select_dir(d)                  # in client mode this goes to the server as a command

    # ── WSJT-X / JTDX stream ──
    def wsjt_apply(self):
        """Settings changed: restart the listener (server) / drop the output socket (client)."""
        if self.wsjt:
            self.wsjt.start()
        rc = self.remote_client
        if rc:
            rc.wsjt_blocked = False
            if rc.state == 'connected':
                rc._wsjt_auth()
        s, self._wsjt_sock = self._wsjt_sock, None
        if s:
            try:
                s.close()
            except OSError:
                pass

    def wsjt_emit(self, b64):
        """Client mode: re-emit one datagram received from the server as local UDP.
        Runs on the network thread; only plain socket calls, no Tk."""
        wc = self.cfg.get('wsjt', {})
        if not wc.get('enabled'):
            return
        try:
            data = base64.b64decode(b64, validate=True)
        except (ValueError, TypeError):
            return
        if len(data) > WSJT_MAX_DGRAM or wsjt_peek(data) is None:
            return
        try:
            if self._wsjt_sock is None:
                s = wsjt_udp_sender((wc.get('outHost') or '127.0.0.1').strip())
                s.bind(('', 0))  # fixed source port: the local program's replies come back to it
                self._wsjt_sock = s
                threading.Thread(target=self._wsjt_reply_loop, args=(s,), daemon=True).start()
            self._wsjt_sock.sendto(data, ((wc.get('outHost') or '127.0.0.1').strip(),
                                          int(wc.get('outPort', WSJT_PORT_DEFAULT))))
            self.wsjt_out_count += 1
        except (OSError, ValueError):
            pass

    def _wsjt_reply_loop(self, s):
        """Client mode: what the local program (WSJT-X, JTDX, GridTracker...) answers to the
        re-emitted stream arrives here. Allowed message types go to the server, if unlocked."""
        s.settimeout(0.5)
        last_warn = 0.0
        while self._wsjt_sock is s:
            try:
                data, _addr = s.recvfrom(65535)
            except socket.timeout:
                continue
            except ConnectionResetError:
                continue
            except OSError:
                break
            info = wsjt_peek(data) if len(data) <= WSJT_MAX_DGRAM else None
            rc = self.remote_client
            if info is None or info[0] not in WSJT_CTL_TYPES or not rc:
                continue
            if not self.cfg.get('wsjt', {}).get('ctlEnabled'):
                continue
            if rc.wsjt_ok:
                rc.send_wsjt(data)
            elif time.time() - last_warn > 10:
                last_warn = time.time()
                self.ui_q.put(lambda: self.toast('WSJT control is not unlocked (check the control password)', err=True))

    def _remote_pin(self, fingerprint):
        self.cfg.setdefault('remote', {})['cFingerprint'] = fingerprint
        save_cfg(self.cfg)

    def _remote_ask_password(self, user, host):
        return simpledialog.askstring('Password', f'Password for {user}@{host}:', show='*', parent=self)

    def _remote_ask_trust(self, fingerprint, host):
        return messagebox.askyesno(
            'Trust this server?',
            f'First connection to {host}.\n\nThe server presented a certificate with SHA-256 fingerprint:\n\n'
            f'{fmt_fingerprint(fingerprint)}\n\n'
            'Compare it with the fingerprint shown on the server (Remote menu, Server section) before '
            'accepting. If it differs, answer No.\n\nTrust this server and remember it?')

    # ── Hamlib integration ──
    def hamlib_started(self, tcp_port):
        """rigctld was just started from the Hamlib tab: point CAT at it."""
        self.cfg.update(catEnabled=True, catHost='127.0.0.1', catPort=tcp_port)
        save_cfg(self.cfg)
        self.var_cat_enabled.set(True)
        self.var_cat_host.set('127.0.0.1')
        self.var_cat_port.set(str(tcp_port))
        self._update_freq_display()
        self.toast(f'rigctld started \u2014 CAT set to 127.0.0.1:{tcp_port}')

    def on_close(self):
        try:
            self.hamlib.shutdown()  # stop rigctld, don't leave it running
        except Exception:
            pass
        self._amp_close_all()
        if self.wsjt:
            self.wsjt.stop()
        if self.pst:
            self.pst.stop()
        for part in (self.remote_server, self.remote_client):
            if part:
                part.stop()
        self.destroy()

    # ── toast / status bar ──
    def toast(self, msg, err=False):
        self.status_var.set(('⚠ ' if err else '') + msg)
        if self.remote_server:
            self.remote_server.broadcast_event(msg, err)


def _cli_admin(args):
    """User / certificate administration from a console, no window needed."""
    import getpass
    store = UserStore()
    try:
        if args.listusers:
            for name, role in store.listing():
                print(f'{name:20} {role}')
            if not store.users:
                print('(no users yet)')
        for name, fn in ((args.adduser, 'add'), (args.setpass, 'pass')):
            if not name:
                continue
            name = name.strip().lower()
            pw = getpass.getpass(f'Password for {name} (min {MIN_PW_LEN} characters): ')
            if pw != getpass.getpass('Repeat: '):
                print('Passwords differ.')
                return 1
            if fn == 'add':
                store.add(name, pw, args.role)
                print(f"User '{name}' added with role {args.role}.")
            else:
                store.set_password(name, pw)
                print(f"Password of '{name}' changed.")
        if args.setctlpass:
            pw = getpass.getpass(f'WSJT control password (min {MIN_PW_LEN} characters): ')
            if pw != getpass.getpass('Repeat: '):
                print('Passwords differ.')
                return 1
            err = UserStore.validate_password(pw)
            if err:
                raise ValueError(err)
            cfg = load_cfg()
            cfg['wsjt']['ctlHash'] = store._make_hash(pw)
            save_cfg(cfg)
            print('WSJT control password set.')
        if args.deluser:
            store.remove(args.deluser.strip().lower())
            print(f"User '{args.deluser}' removed.")
        if args.gencert:
            generate_certificate(side_file('station_cert.pem'), side_file('station_key.pem'))
            print('New certificate created. Clients must re-trust it.')
        if args.fingerprint or args.gencert:
            fp = cert_fingerprint(side_file('station_cert.pem'))
            print('Certificate fingerprint (SHA-256):', fmt_fingerprint(fp) if fp else '(no certificate yet)')
    except (ValueError, RuntimeError) as e:
        print('Error:', e)
        return 1
    return 0


def main(argv=None):
    global CFG_PATH, FORCE_MODE, START_MIN
    ap = argparse.ArgumentParser(prog='stationcontroller', description='Stationcontroller')
    ap.add_argument('--mode', choices=['standalone', 'server', 'client'],
                    help='run in this mode, overriding the saved setting')
    ap.add_argument('--minimized', action='store_true', help='start minimized (handy for an unattended server PC)')
    ap.add_argument('--cfg', metavar='FILE', help='use this settings file (users, certificate and log sit next to it)')
    ap.add_argument('--adduser', metavar='NAME', help='add a user (asks for the password)')
    ap.add_argument('--role', choices=ROLES, default='operator', help='role for --adduser (default: operator)')
    ap.add_argument('--setpass', metavar='NAME', help="change a user's password")
    ap.add_argument('--deluser', metavar='NAME', help='remove a user')
    ap.add_argument('--setctlpass', action='store_true', help='set the WSJT remote-control password')
    ap.add_argument('--listusers', action='store_true', help='list users and roles')
    ap.add_argument('--gencert', action='store_true', help='create a new server certificate')
    ap.add_argument('--fingerprint', action='store_true', help="show the server certificate's fingerprint")
    args = ap.parse_args(argv)
    if args.cfg:
        CFG_PATH = os.path.abspath(args.cfg)
    if any((args.adduser, args.setpass, args.deluser, args.listusers, args.gencert, args.fingerprint, args.setctlpass)):
        return _cli_admin(args)
    FORCE_MODE, START_MIN = args.mode, args.minimized
    App().mainloop()
    return 0


if __name__ == '__main__':
    sys.exit(main())

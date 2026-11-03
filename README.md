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

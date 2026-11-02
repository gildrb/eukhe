# incident_shapes: the shapes of the daemon log lines the incident
# classifier reads (eukhe-types incident/classify.rs and parse.rs; the
# matcher: bend/shape.bend; ids 0-99 of the entry bend/ffi_shape.bend: the
# shape at index i of `table` has id i). Above each shape: the regex it
# replaces (TS src/cli/incident.ts, kept 1:1 by the old Rust patterns.rs).
# `\d` is an ASCII digit here (Rust's is any Unicode digit: an intended
# difference). Pure: no IO, no @unsafe.

import Base
import ./shape.bend as S

# Classes
# -------

# `\S`: no Unicode White_Space
def nws() -> S.Cls:
  S.Cls{S.Space{}, True{}, False{}}

# `\s`: Unicode White_Space
def ws() -> S.Cls:
  S.Cls{S.Space{}, False{}, False{}}

# `[0-9a-f]`
def hex() -> S.Cls:
  S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{97, 102}]}, False{}, False{}}

# `\d`: an ASCII digit
def dig() -> S.Cls:
  S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}

# `.`: any char but a line feed
def dot() -> S.Cls:
  S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}

# `[\s\S]`: any char
def all_chars() -> S.Cls:
  S.Cls{S.Codes{[]}, True{}, False{}}

# `[^"]`
def not_quote() -> S.Cls:
  S.Cls{S.Codes{[S.Rg{34, 34}]}, True{}, False{}}

# `[^\]]`
def not_bracket() -> S.Cls:
  S.Cls{S.Codes{[S.Rg{93, 93}]}, True{}, False{}}

# `c+`
def plus(c: S.Cls) -> S.Piece:
  S.Run{c, 1n, None{}}

# `c*`
def star(c: S.Cls) -> S.Piece:
  S.Run{c, 0n, None{}}

# `^...$`: the whole text
def whole(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.AtStart{}, ps, True{}}

# `^...`: at the text start
def prefix(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.AtStart{}, ps, False{}}

# The shapes
# ----------

# 0 `^(?:eukhe-)?worker-[0-9a-f]+-([0-9a-f]{12})(?:\.sock)?$`
def worker_socket() -> S.Shape:
  whole([S.Opt{[S.Lit{"eukhe-"}]}, S.Lit{"worker-"}, plus(hex()), S.Lit{"-"}, S.Cap{[S.Run{hex(), 12n, Some{12n}}]}, S.Opt{[S.Lit{".sock"}]}])

# 1 `^Session worker ([0-9a-f]{12}) stderr: ?([\s\S]*)$`
def stderr_forward() -> S.Shape:
  whole([S.Lit{"Session worker "}, S.Cap{[S.Run{hex(), 12n, Some{12n}}]}, S.Lit{" stderr:"}, S.Opt{[S.Lit{" "}]}, S.Cap{[star(all_chars())]}])

# 2 `^Eukhe daemon supervisor \S+ listening on \S+$`
def supervisor_listening() -> S.Shape:
  whole([S.Lit{"Eukhe daemon supervisor "}, plus(nws()), S.Lit{" listening on "}, plus(nws())])

# 3 `^Eukhe daemon listening on \S+$`
def worker_listening() -> S.Shape:
  whole([S.Lit{"Eukhe daemon listening on "}, plus(nws())])

# 4 `^(?:uncaught exception|unhandled rejection): (.+)$`
def crash_line() -> S.Shape:
  whole([S.Alt{[S.Lit{"uncaught exception"}], [S.Lit{"unhandled rejection"}]}, S.Lit{": "}, S.Cap{[plus(dot())]}])

# 5 `^(?:uncaught exception|unhandled rejection): `
def crash_prefix() -> S.Shape:
  prefix([S.Alt{[S.Lit{"uncaught exception"}], [S.Lit{"unhandled rejection"}]}, S.Lit{": "}])

# 6 `^shutting down \(exit (\d+)\); closing (\d+) active session\(s\)$`
def shutdown_exit() -> S.Shape:
  whole([S.Lit{"shutting down (exit "}, S.Cap{[plus(dig())]}, S.Lit{"); closing "}, S.Cap{[plus(dig())]}, S.Lit{" active session(s)"}])

# 7 `^received (\S+); shutting down$`
def signal_shutdown() -> S.Shape:
  whole([S.Lit{"received "}, S.Cap{[plus(nws())]}, S.Lit{"; shutting down"}])

# 8 `^shutdown command received over socket; (\d+) active session\(s\) will be closed$`
def stop_requested() -> S.Shape:
  whole([S.Lit{"shutdown command received over socket; "}, S.Cap{[plus(dig())]}, S.Lit{" active session(s) will be closed"}])

# 9 `^Passivated idle child sessionId=(\S+) name=("[^"]*"|\S+) idleMinutes=(\d+)$`
def passivated() -> S.Shape:
  whole([S.Lit{"Passivated idle child sessionId="}, S.Cap{[plus(nws())]}, S.Lit{" name="}, S.Cap{[S.Alt{[S.Lit{"\""}, star(not_quote()), S.Lit{"\""}], [plus(nws())]}]}, S.Lit{" idleMinutes="}, S.Cap{[plus(dig())]}])

# 10 `^Daemon supervisor startup failed: (.+)$`
def startup_failed() -> S.Shape:
  whole([S.Lit{"Daemon supervisor startup failed: "}, S.Cap{[plus(dot())]}])

# 11 `^Supervisor command (\S+) failed: (.+)$`
def supervisor_command() -> S.Shape:
  whole([S.Lit{"Supervisor command "}, S.Cap{[plus(nws())]}, S.Lit{" failed: "}, S.Cap{[plus(dot())]}])

# 12 `^daemon command "([^"]+)" failed: (.+)$`
def daemon_command() -> S.Shape:
  whole([S.Lit{"daemon command \""}, S.Cap{[plus(not_quote())]}, S.Lit{"\" failed: "}, S.Cap{[plus(dot())]}])

# 13 `^(?:Failed|could not)(?: to)? catch up (?:snapshot )?client \S+(?: for (\S+))?: (.+)$`
def catch_up() -> S.Shape:
  whole([S.Alt{[S.Lit{"Failed"}], [S.Lit{"could not"}]}, S.Opt{[S.Lit{" to"}]}, S.Lit{" catch up "}, S.Opt{[S.Lit{"snapshot "}]}, S.Lit{"client "}, plus(nws()), S.Opt{[S.Lit{" for "}, S.Cap{[plus(nws())]}]}, S.Lit{": "}, S.Cap{[plus(dot())]}])

# 14 `^Could not list heartbeats from a worker: (.+)$`
def heartbeats_list() -> S.Shape:
  whole([S.Lit{"Could not list heartbeats from a worker: "}, S.Cap{[plus(dot())]}])

# 15 `^Recovered worker (\S+) without replaying uncertain operations: (.+)$`
def recovered() -> S.Shape:
  whole([S.Lit{"Recovered worker "}, S.Cap{[plus(nws())]}, S.Lit{" without replaying uncertain operations: "}, S.Cap{[plus(dot())]}])

# 16 `^Recovered worker (\S+)$`
def recovered_plain() -> S.Shape:
  whole([S.Lit{"Recovered worker "}, S.Cap{[plus(nws())]}])

# 17 `^Could not adopt worker (\S+): (.+)$`
def adopt_failed() -> S.Shape:
  whole([S.Lit{"Could not adopt worker "}, S.Cap{[plus(nws())]}, S.Lit{": "}, S.Cap{[plus(dot())]}])

# 18 `^Could not recover worker (\S+): (.+)$`
def recover_failed() -> S.Shape:
  whole([S.Lit{"Could not recover worker "}, S.Cap{[plus(nws())]}, S.Lit{": "}, S.Cap{[plus(dot())]}])

# 19 `^Worker (\S+) failed after three recovery attempts$`
def failed_after_retries() -> S.Shape:
  whole([S.Lit{"Worker "}, S.Cap{[plus(nws())]}, S.Lit{" failed after three recovery attempts"}])

# 20 `^Worker (\S+) is unresponsive; parked failed after \d+ probe rounds$`
def unresponsive() -> S.Shape:
  whole([S.Lit{"Worker "}, S.Cap{[plus(nws())]}, S.Lit{" is unresponsive; parked failed after "}, plus(dig()), S.Lit{" probe rounds"}])

# 21 `^Reclaimed stale registration for stopped worker (\S+)$`
def reclaimed() -> S.Shape:
  whole([S.Lit{"Reclaimed stale registration for stopped worker "}, S.Cap{[plus(nws())]}])

# 22 `^Migrated (\d+) scheduled jobs into session artifacts$`
def migrated() -> S.Shape:
  whole([S.Lit{"Migrated "}, S.Cap{[plus(dig())]}, S.Lit{" scheduled jobs into session artifacts"}])

# 23 `^launched replacement supervisor on \S+$`
def replacement() -> S.Shape:
  whole([S.Lit{"launched replacement supervisor on "}, plus(nws())])

# 24 `^Woke session worker for a due scheduled job: \S+$`
def woke() -> S.Shape:
  whole([S.Lit{"Woke session worker for a due scheduled job: "}, plus(nws())])

# 25 `^Evicted idle worker (\S+) root=\S* idleMinutes=(\d+) sessions=(\d+)$`
def evicted_idle() -> S.Shape:
  whole([S.Lit{"Evicted idle worker "}, S.Cap{[plus(nws())]}, S.Lit{" root="}, star(nws()), S.Lit{" idleMinutes="}, S.Cap{[plus(dig())]}, S.Lit{" sessions="}, S.Cap{[plus(dig())]}])

# 26 `^Evicted empty session worker (\S+) root=\S+ on last client detach$`
def evicted_empty() -> S.Shape:
  whole([S.Lit{"Evicted empty session worker "}, S.Cap{[plus(nws())]}, S.Lit{" root="}, plus(nws()), S.Lit{" on last client detach"}])

# 27 `(?i)authentication failed`
def auth_failed() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Fold{"authentication failed"}], False{}}

# 28 `Unknown active session: (\S+)`
def unknown_session() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Lit{"Unknown active session: "}, S.Cap{[plus(nws())]}], False{}}

# 29 `^\s*at\s`
def stack_frame() -> S.Shape:
  prefix([star(ws()), S.Lit{"at"}, S.Run{ws(), 1n, Some{1n}}])

# 30 `^\[([^\]]+)\]\s*(.*)$`
def daemon_line() -> S.Shape:
  whole([S.Lit{"["}, S.Cap{[plus(not_bracket())]}, S.Lit{"]"}, star(ws()), S.Cap{[star(dot())]}])

# The table: the shape of id i at index i
def table() -> List<&2, S.Shape>:
  [worker_socket(), stderr_forward(), supervisor_listening(), worker_listening(), crash_line(), crash_prefix(), shutdown_exit(), signal_shutdown(), stop_requested(), passivated(), startup_failed(), supervisor_command(), daemon_command(), catch_up(), heartbeats_list(), recovered(), recovered_plain(), adopt_failed(), recover_failed(), failed_after_retries(), unresponsive(), reclaimed(), migrated(), replacement(), woke(), evicted_idle(), evicted_empty(), auth_failed(), unknown_session(), stack_frame(), daemon_line()]

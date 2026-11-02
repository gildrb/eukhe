# incident_shapes: the shapes of the daemon log lines the incident
# classifier reads (eukhe-types incident/classify.rs and parse.rs; the
# matcher: bend/shape.bend; ids 0-99 of the entry bend/ffi_shape.bend: the
# shape at index i of `table` has id i). Above each shape: the regex it
# replaces (TS src/cli/incident.ts, kept 1:1 by the old Rust patterns.rs).
# `\d` is an ASCII digit here (Rust's is any Unicode digit: an intended
# difference). Each shape is written out whole, so the compiled core holds
# it as a constant. Pure: no IO, no @unsafe.

import Base
import ./shape.bend as S

# 0 `^(?:eukhe-)?worker-[0-9a-f]+-([0-9a-f]{12})(?:\.sock)?$`
def worker_socket() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Opt{[S.Lit{"eukhe-"}]}, S.Lit{"worker-"}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{97, 102}]}, False{}, False{}}, 1n, None{}}, S.Lit{"-"}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{97, 102}]}, False{}, False{}}, 12n, Some{12n}}]}, S.Opt{[S.Lit{".sock"}]}], True{}}

# 1 `^Session worker ([0-9a-f]{12}) stderr: ?([\s\S]*)$`
def stderr_forward() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Session worker "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{97, 102}]}, False{}, False{}}, 12n, Some{12n}}]}, S.Lit{" stderr:"}, S.Opt{[S.Lit{" "}]}, S.Cap{[S.Run{S.Cls{S.Codes{[]}, True{}, False{}}, 0n, None{}}]}], True{}}

# 2 `^Eukhe daemon supervisor \S+ listening on \S+$`
def supervisor_listening() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Eukhe daemon supervisor "}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}, S.Lit{" listening on "}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}], True{}}

# 3 `^Eukhe daemon listening on \S+$`
def worker_listening() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Eukhe daemon listening on "}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}], True{}}

# 4 `^(?:uncaught exception|unhandled rejection): (.+)$`
def crash_line() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Alt{[S.Lit{"uncaught exception"}], [S.Lit{"unhandled rejection"}]}, S.Lit{": "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 1n, None{}}]}], True{}}

# 5 `^(?:uncaught exception|unhandled rejection): `
def crash_prefix() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Alt{[S.Lit{"uncaught exception"}], [S.Lit{"unhandled rejection"}]}, S.Lit{": "}], False{}}

# 6 `^shutting down \(exit (\d+)\); closing (\d+) active session\(s\)$`
def shutdown_exit() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"shutting down (exit "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}, 1n, None{}}]}, S.Lit{"); closing "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}, 1n, None{}}]}, S.Lit{" active session(s)"}], True{}}

# 7 `^received (\S+); shutting down$`
def signal_shutdown() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"received "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}, S.Lit{"; shutting down"}], True{}}

# 8 `^shutdown command received over socket; (\d+) active session\(s\) will be closed$`
def stop_requested() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"shutdown command received over socket; "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}, 1n, None{}}]}, S.Lit{" active session(s) will be closed"}], True{}}

# 9 `^Passivated idle child sessionId=(\S+) name=("[^"]*"|\S+) idleMinutes=(\d+)$`
def passivated() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Passivated idle child sessionId="}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}, S.Lit{" name="}, S.Cap{[S.Alt{[S.Lit{"\""}, S.Run{S.Cls{S.Codes{[S.Rg{34, 34}]}, True{}, False{}}, 0n, None{}}, S.Lit{"\""}], [S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}]}, S.Lit{" idleMinutes="}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}, 1n, None{}}]}], True{}}

# 10 `^Daemon supervisor startup failed: (.+)$`
def startup_failed() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Daemon supervisor startup failed: "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 1n, None{}}]}], True{}}

# 11 `^Supervisor command (\S+) failed: (.+)$`
def supervisor_command() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Supervisor command "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}, S.Lit{" failed: "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 1n, None{}}]}], True{}}

# 12 `^daemon command "([^"]+)" failed: (.+)$`
def daemon_command() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"daemon command \""}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}]}, True{}, False{}}, 1n, None{}}]}, S.Lit{"\" failed: "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 1n, None{}}]}], True{}}

# 13 `^(?:Failed|could not)(?: to)? catch up (?:snapshot )?client \S+(?: for (\S+))?: (.+)$`
def catch_up() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Alt{[S.Lit{"Failed"}], [S.Lit{"could not"}]}, S.Opt{[S.Lit{" to"}]}, S.Lit{" catch up "}, S.Opt{[S.Lit{"snapshot "}]}, S.Lit{"client "}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}, S.Opt{[S.Lit{" for "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}]}, S.Lit{": "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 1n, None{}}]}], True{}}

# 14 `^Could not list heartbeats from a worker: (.+)$`
def heartbeats_list() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Could not list heartbeats from a worker: "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 1n, None{}}]}], True{}}

# 15 `^Recovered worker (\S+) without replaying uncertain operations: (.+)$`
def recovered() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Recovered worker "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}, S.Lit{" without replaying uncertain operations: "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 1n, None{}}]}], True{}}

# 16 `^Recovered worker (\S+)$`
def recovered_plain() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Recovered worker "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}], True{}}

# 17 `^Could not adopt worker (\S+): (.+)$`
def adopt_failed() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Could not adopt worker "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}, S.Lit{": "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 1n, None{}}]}], True{}}

# 18 `^Could not recover worker (\S+): (.+)$`
def recover_failed() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Could not recover worker "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}, S.Lit{": "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 1n, None{}}]}], True{}}

# 19 `^Worker (\S+) failed after three recovery attempts$`
def failed_after_retries() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Worker "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}, S.Lit{" failed after three recovery attempts"}], True{}}

# 20 `^Worker (\S+) is unresponsive; parked failed after \d+ probe rounds$`
def unresponsive() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Worker "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}, S.Lit{" is unresponsive; parked failed after "}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}, 1n, None{}}, S.Lit{" probe rounds"}], True{}}

# 21 `^Reclaimed stale registration for stopped worker (\S+)$`
def reclaimed() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Reclaimed stale registration for stopped worker "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}], True{}}

# 22 `^Migrated (\d+) scheduled jobs into session artifacts$`
def migrated() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Migrated "}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}, 1n, None{}}]}, S.Lit{" scheduled jobs into session artifacts"}], True{}}

# 23 `^launched replacement supervisor on \S+$`
def replacement() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"launched replacement supervisor on "}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}], True{}}

# 24 `^Woke session worker for a due scheduled job: \S+$`
def woke() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Woke session worker for a due scheduled job: "}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}], True{}}

# 25 `^Evicted idle worker (\S+) root=\S* idleMinutes=(\d+) sessions=(\d+)$`
def evicted_idle() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Evicted idle worker "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}, S.Lit{" root="}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 0n, None{}}, S.Lit{" idleMinutes="}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}, 1n, None{}}]}, S.Lit{" sessions="}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}, 1n, None{}}]}], True{}}

# 26 `^Evicted empty session worker (\S+) root=\S+ on last client detach$`
def evicted_empty() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"Evicted empty session worker "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}, S.Lit{" root="}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}, S.Lit{" on last client detach"}], True{}}

# 27 `(?i)authentication failed`
def auth_failed() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Fold{"authentication failed"}], False{}}

# 28 `Unknown active session: (\S+)`
def unknown_session() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Lit{"Unknown active session: "}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}], False{}}

# 29 `^\s*at\s`
def stack_frame() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}, S.Lit{"at"}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 1n, Some{1n}}], False{}}

# 30 `^\[([^\]]+)\]\s*(.*)$`
def daemon_line() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"["}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{93, 93}]}, True{}, False{}}, 1n, None{}}]}, S.Lit{"]"}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 0n, None{}}]}], True{}}

# The table: the shape of id i at index i
def table() -> List<&2, S.Shape>:
  [worker_socket(), stderr_forward(), supervisor_listening(), worker_listening(), crash_line(), crash_prefix(), shutdown_exit(), signal_shutdown(), stop_requested(), passivated(), startup_failed(), supervisor_command(), daemon_command(), catch_up(), heartbeats_list(), recovered(), recovered_plain(), adopt_failed(), recover_failed(), failed_after_retries(), unresponsive(), reclaimed(), migrated(), replacement(), woke(), evicted_idle(), evicted_empty(), auth_failed(), unknown_session(), stack_frame(), daemon_line()]


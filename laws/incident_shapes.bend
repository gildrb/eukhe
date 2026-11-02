# eukhe: the laws of area incident_shapes

import Base
import ../bend/shape.bend as S
import ../bend/incident_shapes.bend as IS

# (IS1) The shapes of the daemon log lines the incident classifier reads
# ---------------------------------------------------------------------
# bend/incident_shapes.bend, ids 0-99 of the entry bend/ffi_shape.bend
# (eukhe-types incident/classify.rs and parse.rs ask them through
# eukhe-bend rules/shape.rs, in place of their `regex` patterns). The
# matcher is pinned by laws/shape/match.bend and laws/shape/search.bend.
# "a token" is one or more chars that are no White_Space (regex `\S+`); "a
# number" one or more ASCII digits 0-9 (Rust's `\d` takes every Unicode
# digit: an intended difference); "the rest of the line" one or more chars
# that are no line feed (regex `.+`); "hex" a char 0-9 or a-f. "the line
# is" a shape read at the text start that must end the text; "the line
# starts with" one read at the text start; "the text holds" one read
# anywhere. Captures are numbered in order from 1.
#
# R1: id 0, a worker socket name: the line is `eukhe-` or nothing, then
#     `worker-`, then one or more hex, then `-`, then exactly twelve hex
#     (captured: the worker id), then `.sock` or nothing.
# R2: id 1, a worker's stderr forwarded: the line is `Session worker `,
#     then exactly twelve hex (captured: the worker), then ` stderr:`,
#     then a space or nothing, then any chars at all, line feeds too
#     (captured: the body).
# R3: id 2, the supervisor listening: the line is `Eukhe daemon supervisor `,
#     a token, ` listening on `, a token.
# R4: id 3, a worker listening: the line is `Eukhe daemon listening on `,
#     then a token.
# R5: id 4, a crash: the line is `uncaught exception` or `unhandled
#     rejection`, then `: `, then the rest of the line (captured).
# R6: id 5, a crash's start: the line starts with `uncaught exception` or
#     `unhandled rejection`, then `: `.
# R7: id 6, a worker exit: the line is `shutting down (exit `, a number
#     (captured: the exit code), `); closing `, a number (captured: the
#     sessions), ` active session(s)`.
# R8: id 7, a signal: the line is `received `, a token (captured: the
#     signal), `; shutting down`.
# R9: id 8, a stop request: the line is `shutdown command received over
#     socket; `, a number (captured: the sessions), ` active session(s)
#     will be closed`.
# R10: id 9, a passivated child: the line is `Passivated idle child
#     sessionId=`, a token (captured: the session), ` name=`, then
#     (captured: the name) either `"`, any chars that are no `"`, `"`, or
#     else a token; then ` idleMinutes=`, a number (captured: the minutes).
# R11: id 10, a failed supervisor start: the line is `Daemon supervisor
#     startup failed: `, the rest of the line (captured: the error).
# R12: id 11, a failed supervisor command: the line is `Supervisor command `,
#     a token (captured: the command), ` failed: `, the rest of the line
#     (captured: the error).
# R13: id 12, a failed daemon command: the line is `daemon command "`, one
#     or more chars that are no `"` (captured: the command), `" failed: `,
#     the rest of the line (captured: the error).
# R14: id 13, a failed client catch-up: the line is `Failed` or `could
#     not`, then ` to` or nothing, then ` catch up `, then `snapshot ` or
#     nothing, then `client `, a token, then either ` for ` and a token
#     (captured: the session) or nothing, then `: `, the rest of the line
#     (captured: the error).
# R15: id 14, a failed heartbeat list: the line is `Could not list
#     heartbeats from a worker: `, the rest of the line (captured).
# R16: id 15, a recovery with uncertain operations: the line is `Recovered
#     worker `, a token (captured: the worker), ` without replaying
#     uncertain operations: `, the rest of the line (captured: the
#     operations).
# R17: id 16, a recovery: the line is `Recovered worker `, a token
#     (captured: the worker).
# R18: id 17, a failed adoption: the line is `Could not adopt worker `, a
#     token (captured: the worker), `: `, the rest of the line (captured).
# R19: id 18, a failed recovery: the line is `Could not recover worker `, a
#     token (captured: the worker), `: `, the rest of the line (captured).
# R20: id 19, a worker given up: the line is `Worker `, a token (captured:
#     the worker), ` failed after three recovery attempts`.
# R21: id 20, an unresponsive worker: the line is `Worker `, a token
#     (captured: the worker), ` is unresponsive; parked failed after `, a
#     number, ` probe rounds`.
# R22: id 21, a reclaimed registration: the line is `Reclaimed stale
#     registration for stopped worker `, a token (captured: the worker).
# R23: id 22, migrated jobs: the line is `Migrated `, a number (captured),
#     ` scheduled jobs into session artifacts`.
# R24: id 23, a replacement supervisor: the line is `launched replacement
#     supervisor on `, a token.
# R25: id 24, a scheduled wake: the line is `Woke session worker for a due
#     scheduled job: `, a token.
# R26: id 25, an idle eviction: the line is `Evicted idle worker `, a token
#     (captured: the worker), ` root=`, any chars that are no White_Space
#     (none too), ` idleMinutes=`, a number (captured), ` sessions=`, a
#     number (captured).
# R27: id 26, an empty eviction: the line is `Evicted empty session worker `,
#     a token (captured: the worker), ` root=`, a token, ` on last client
#     detach`.
# R28: id 27, a failed authentication: the text holds `authentication
#     failed`, ASCII letters in either case (Rust's `(?i)` also takes the
#     Kelvin sign and the long s, neither in these words).
# R29: id 28, an unknown session: the text holds `Unknown active session: `
#     then a token (captured: the session).
# R30: id 29, a stack frame: the line starts with any White_Space chars
#     (none too), `at`, then exactly one White_Space char.
# R31: id 30, a daemon log line: the line is `[`, one or more chars that
#     are no `]` (captured: the time), `]`, any White_Space chars (none
#     too), then any chars that are no line feed (none too; captured: the
#     message).
# R32: the table holds exactly these shapes, the one of id i at index i,
#     and no other.

# Spec helpers
# ------------

# a char that is no White_Space; a White_Space char
def sp_dark() -> S.Cls:
  S.Cls{S.Space{}, True{}, False{}}

def sp_blank() -> S.Cls:
  S.Cls{S.Space{}, False{}, False{}}

# a char none of the codes c
def sp_but(+c: U32) -> S.Cls:
  S.Cls{S.Codes{[S.Rg{c, c}]}, True{}, False{}}

# hex: 0-9 (48-57) or a-f (97-102); an ASCII digit 0-9
def sp_hex() -> S.Cls:
  S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{97, 102}]}, False{}, False{}}

def sp_digit() -> S.Cls:
  S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}

def sp_token() -> S.Piece:
  S.Run{sp_dark(), 1n, None{}}

def sp_number() -> S.Piece:
  S.Run{sp_digit(), 1n, None{}}

# the rest of the line: one or more chars that are no line feed (10)
def sp_rest() -> S.Piece:
  S.Run{sp_but(10), 1n, None{}}

def sp_twelve_hex() -> S.Piece:
  S.Run{sp_hex(), 12n, Some{12n}}

def sp_t(s: String) -> S.Piece:
  S.Lit{s}

def sp_cap(p: S.Piece) -> S.Piece:
  S.Cap{[p]}

def sp_or(a: String, b: String) -> S.Piece:
  S.Alt{[S.Lit{a}], [S.Lit{b}]}

def sp_or_none(a: String) -> S.Piece:
  S.Opt{[S.Lit{a}]}

def sp_line(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.AtStart{}, ps, True{}}

def sp_starts(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.AtStart{}, ps, False{}}

def sp_holds(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.Anywhere{}, ps, False{}}

# R1-R31, by id
def sp_table() -> List<&2, S.Shape>:
  [sp_line([sp_or_none("eukhe-"), sp_t("worker-"), S.Run{sp_hex(), 1n, None{}}, sp_t("-"), sp_cap(sp_twelve_hex()), sp_or_none(".sock")]),
   sp_line([sp_t("Session worker "), sp_cap(sp_twelve_hex()), sp_t(" stderr:"), sp_or_none(" "), sp_cap(S.Run{S.Cls{S.Codes{[]}, True{}, False{}}, 0n, None{}})]),
   sp_line([sp_t("Eukhe daemon supervisor "), sp_token(), sp_t(" listening on "), sp_token()]),
   sp_line([sp_t("Eukhe daemon listening on "), sp_token()]),
   sp_line([sp_or("uncaught exception", "unhandled rejection"), sp_t(": "), sp_cap(sp_rest())]),
   sp_starts([sp_or("uncaught exception", "unhandled rejection"), sp_t(": ")]),
   sp_line([sp_t("shutting down (exit "), sp_cap(sp_number()), sp_t("); closing "), sp_cap(sp_number()), sp_t(" active session(s)")]),
   sp_line([sp_t("received "), sp_cap(sp_token()), sp_t("; shutting down")]),
   sp_line([sp_t("shutdown command received over socket; "), sp_cap(sp_number()), sp_t(" active session(s) will be closed")]),
   sp_line([sp_t("Passivated idle child sessionId="), sp_cap(sp_token()), sp_t(" name="), S.Cap{[S.Alt{[sp_t("\""), S.Run{sp_but(34), 0n, None{}}, sp_t("\"")], [sp_token()]}]}, sp_t(" idleMinutes="), sp_cap(sp_number())]),
   sp_line([sp_t("Daemon supervisor startup failed: "), sp_cap(sp_rest())]),
   sp_line([sp_t("Supervisor command "), sp_cap(sp_token()), sp_t(" failed: "), sp_cap(sp_rest())]),
   sp_line([sp_t("daemon command \""), sp_cap(S.Run{sp_but(34), 1n, None{}}), sp_t("\" failed: "), sp_cap(sp_rest())]),
   sp_line([sp_or("Failed", "could not"), sp_or_none(" to"), sp_t(" catch up "), sp_or_none("snapshot "), sp_t("client "), sp_token(), S.Opt{[sp_t(" for "), sp_cap(sp_token())]}, sp_t(": "), sp_cap(sp_rest())]),
   sp_line([sp_t("Could not list heartbeats from a worker: "), sp_cap(sp_rest())]),
   sp_line([sp_t("Recovered worker "), sp_cap(sp_token()), sp_t(" without replaying uncertain operations: "), sp_cap(sp_rest())]),
   sp_line([sp_t("Recovered worker "), sp_cap(sp_token())]),
   sp_line([sp_t("Could not adopt worker "), sp_cap(sp_token()), sp_t(": "), sp_cap(sp_rest())]),
   sp_line([sp_t("Could not recover worker "), sp_cap(sp_token()), sp_t(": "), sp_cap(sp_rest())]),
   sp_line([sp_t("Worker "), sp_cap(sp_token()), sp_t(" failed after three recovery attempts")]),
   sp_line([sp_t("Worker "), sp_cap(sp_token()), sp_t(" is unresponsive; parked failed after "), sp_number(), sp_t(" probe rounds")]),
   sp_line([sp_t("Reclaimed stale registration for stopped worker "), sp_cap(sp_token())]),
   sp_line([sp_t("Migrated "), sp_cap(sp_number()), sp_t(" scheduled jobs into session artifacts")]),
   sp_line([sp_t("launched replacement supervisor on "), sp_token()]),
   sp_line([sp_t("Woke session worker for a due scheduled job: "), sp_token()]),
   sp_line([sp_t("Evicted idle worker "), sp_cap(sp_token()), sp_t(" root="), S.Run{sp_dark(), 0n, None{}}, sp_t(" idleMinutes="), sp_cap(sp_number()), sp_t(" sessions="), sp_cap(sp_number())]),
   sp_line([sp_t("Evicted empty session worker "), sp_cap(sp_token()), sp_t(" root="), sp_token(), sp_t(" on last client detach")]),
   sp_holds([S.Fold{"authentication failed"}]),
   sp_holds([sp_t("Unknown active session: "), sp_cap(sp_token())]),
   sp_starts([S.Run{sp_blank(), 0n, None{}}, sp_t("at"), S.Run{sp_blank(), 1n, Some{1n}}]),
   sp_line([sp_t("["), sp_cap(S.Run{sp_but(93), 1n, None{}}), sp_t("]"), S.Run{sp_blank(), 0n, None{}}, sp_cap(S.Run{sp_but(10), 0n, None{}})])]

# Laws
# ----

# LAW incident_shapes_table (R1-R32): the table is exactly the shapes R1-R31
# state, by id
# EXCLUDES: a shape that drifts from the regex it replaced (a piece lost,
#   added or reordered, a capture moved, another class, a shape read
#   anywhere that must start the line, a missing end), ids shifted
# waive L4-examples-only: the shapes and the table are constants, no input
#   to leave free; this law pins the table whole to R1-R31
law incident_shapes_table:
  {IS.table() == sp_table() : List<&2, S.Shape>}

# LAW incident_shapes_socket_example (R1): anchor: a worker socket name
# from the classifier's tests gives its worker id; a daemon socket none
# EXCLUDES: a table that drifts from the classifier's tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   incident_shapes_table pins it whole to its R rule
law incident_shapes_socket_example:
  {[S.first([IS.worker_socket()], "worker-98ed5cb228d2-5b1d3aeb91ee.sock"), S.first([IS.worker_socket()], "daemon.sock")] == [Some{S.Found{0n, S.Fit{0n, 37n, [Some{"5b1d3aeb91ee"}]}}}, None{}] : List<&2, Maybe<&2, S.Found>>}

# the shapes the classifier asks of a worker's stderr body's first line, in
# its order (classify.rs classify_worker_stderr_body)
def ex_body() -> List<&2, S.Shape>:
  [IS.worker_listening(), IS.crash_line(), IS.shutdown_exit(), IS.signal_shutdown(), IS.stop_requested(), IS.passivated()]

# the shapes the classifier asks of a supervisor or worker line, in its
# order (classify.rs classify_incident_entry)
def ex_line() -> List<&2, S.Shape>:
  [IS.supervisor_listening(), IS.startup_failed(), IS.supervisor_command(), IS.daemon_command(), IS.catch_up(), IS.heartbeats_list(), IS.recovered(), IS.recovered_plain(), IS.adopt_failed(), IS.recover_failed(), IS.failed_after_retries(), IS.unresponsive(), IS.reclaimed(), IS.migrated(), IS.replacement(), IS.woke(), IS.evicted_idle(), IS.evicted_empty()]

# LAW incident_shapes_stderr_example (R2, R30): anchor: a forwarded crash
# from the classifier's tests gives the worker and the body; the stack
# frame body after it starts a stack frame
# EXCLUDES: a table that drifts from the classifier's tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   incident_shapes_table pins it whole to its R rule
law incident_shapes_stderr_example:
  {[S.first([IS.stderr_forward()], "Session worker 5b1d3aeb91ee stderr: uncaught exception: Error: write EPIPE"), S.first([IS.stack_frame()], "    at afterWriteDispatched (node:internal/stream_base_commons:159:15)")] == [Some{S.Found{0n, S.Fit{0n, 74n, [Some{"5b1d3aeb91ee"}, Some{"uncaught exception: Error: write EPIPE"}]}}}, Some{S.Found{0n, S.Fit{0n, 7n, []}}}] : List<&2, Maybe<&2, S.Found>>}

# LAW incident_shapes_body_example (R4-R10): anchor: in the order the
# classifier asks them, a passivation with an empty name is the sixth shape
# (the name captured with its quotes) and a crash the second
# EXCLUDES: a table that drifts from the classifier's tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   incident_shapes_table pins it whole to its R rule
law incident_shapes_body_example:
  {[S.first(ex_body(), "Passivated idle child sessionId=feedface1234 name=\"\" idleMinutes=5"), S.first(ex_body(), "uncaught exception: Error: write EPIPE")] == [Some{S.Found{5n, S.Fit{0n, 66n, [Some{"feedface1234"}, Some{"\"\""}, Some{"5"}]}}}, Some{S.Found{1n, S.Fit{0n, 38n, [Some{"Error: write EPIPE"}]}}}] : List<&2, Maybe<&2, S.Found>>}

# LAW incident_shapes_line_example (R3, R11-R27): anchor: in the order the
# classifier asks them, a failed supervisor command is the third shape and
# a recovery with operations the seventh (not the plain recovery after it)
# EXCLUDES: a table that drifts from the classifier's tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   incident_shapes_table pins it whole to its R rule
law incident_shapes_line_example:
  {[S.first(ex_line(), "Supervisor command attach failed: Error: Timed out waiting for daemon worker response to attach"), S.first(ex_line(), "Recovered worker 5b1d3aeb91ee without replaying uncertain operations: b, b, a, c, d, e")] == [Some{S.Found{2n, S.Fit{0n, 95n, [Some{"attach"}, Some{"Error: Timed out waiting for daemon worker response to attach"}]}}}, Some{S.Found{6n, S.Fit{0n, 86n, [Some{"5b1d3aeb91ee"}, Some{"b, b, a, c, d, e"}]}}}] : List<&2, Maybe<&2, S.Found>>}

# LAW incident_shapes_command_example (R28, R29): anchor: a command error
# body holds a failed authentication in any case, or an unknown session
# EXCLUDES: a table that drifts from the classifier's tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   incident_shapes_table pins it whole to its R rule
law incident_shapes_command_example:
  {[S.first([IS.auth_failed(), IS.unknown_session()], "Error: Worker authentication failed"), S.first([IS.auth_failed(), IS.unknown_session()], "Error: Unknown active session: aabbccddeeff")] == [Some{S.Found{0n, S.Fit{14n, 35n, []}}}, Some{S.Found{1n, S.Fit{7n, 43n, [Some{"aabbccddeeff"}]}}}] : List<&2, Maybe<&2, S.Found>>}

# LAW incident_shapes_daemon_line_example (R31): anchor: a per-daemon log
# line from the parser's tests gives its time and message; no brackets, or
# nothing inside them, is no daemon line
# EXCLUDES: a table that drifts from the parser's tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   incident_shapes_table pins it whole to its R rule
law incident_shapes_daemon_line_example:
  {[S.first([IS.daemon_line()], "[2026-09-10T20:23:24.945Z] uncaught exception: Error: write EPIPE"), S.first([IS.daemon_line()], "[]"), S.first([IS.daemon_line()], "not a log line")] == [Some{S.Found{0n, S.Fit{0n, 65n, [Some{"2026-09-10T20:23:24.945Z"}, Some{"uncaught exception: Error: write EPIPE"}]}}}, None{}, None{}] : List<&2, Maybe<&2, S.Found>>}

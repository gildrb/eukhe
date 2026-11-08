# ffi_tool_call: the stepper of the compiled Bend core for one tool call's
# journal (crates/eukhe-durable/src/harness/tool/invocation.rs): its state
# is the call of bend/tool_call.bend, kept in the Bend heap. The Harness
# opens it where it journals the call's start, sends each report and the
# end of the tool's execute as they come, and does what each reply says.
# The same entry's call `ffi` is the effect gate of bend/tool_call.bend
# (crates/eukhe-durable/src/harness/tool.rs asks it at each handler of a
# tool task). The codec is the wire format of bend/wire.bend
# (crates/eukhe-bend/WIRE.md):
#
#   open    first: Bool (a first attempt, not a rerun)   reply: Rec
#   step    Ev                                           reply: Act
#   Rec     0 began (the slot goes running), 1 cleared (a rerun clears it)
#   Ev      0 a report | 1 threw: Bool, aborted: Bool (the execute's end)
#   Act     0 keep | 1 refuse | 2 how (settle) | 3 late
#   How     0 finished, 1 failed, 2 cancelled
#
#   ffi     Gate                                         reply: Go
#   Gate    0 enter: found: Bool, tool: Now
#           | 1 recover: found: Bool, stored: Replay, tool: Now
#           | 2 stop: found: Bool, restart: Bool, intent: Bool
#   Now     0 gone | 1 offered: Replay
#   Replay  0 safe, 1 unsafe
#   Go      0 run, 1 missing, 2 unavailable, 3 rerun, 4 interrupted,
#           5 aborted, 6 abandoned
#
# A malformed event, or one with input left over, answers the error form
# and keeps the call; a malformed open opens the refused state, which
# answers every step with the error form; a call input that is not exactly
# one Gate answers `E tool_call: malformed gate`. laws/tool_call.bend pins
# the entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./tool_call.bend as T

# Decoders
# --------

def get_ev.aborted(t: Bool, r: W.Dec<Bool>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{a, s}:
      W.Got{T.End{t, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.threw(r: W.Dec<Bool>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{t, s}:
      get_ev.aborted(t, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(n: Nat, s: String) -> W.Dec<T.Ev>:
  match n:
    case 0n:
      W.Got{T.Report{}, s}
    case 1n:
      get_ev.threw(W.get_bool(s))
    case 2n+p:
      W.Bad{}

def get_ev.go(r: W.Dec<Nat>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{n, s}:
      get_ev.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the event at the start of s
def get_ev(s: String) -> W.Dec<T.Ev>:
  get_ev.go(W.get_nat(s))

# Encoders
# --------

def put_rec(r: T.Rec) -> String:
  match r:
    case T.Began{}:
      W.put_nat(0n, "")
    case T.Cleared{}:
      W.put_nat(1n, "")

def put_how(h: T.How) -> String:
  match h:
    case T.Finished{}:
      W.put_nat(0n, "")
    case T.Failed{}:
      W.put_nat(1n, "")
    case T.Cancelled{}:
      W.put_nat(2n, "")

def put_act(a: T.Act) -> String:
  match a:
    case T.Keep{}:
      W.put_nat(0n, "")
    case T.Refuse{}:
      W.put_nat(1n, "")
    case T.Settle{h}:
      W.put_nat(2n, put_how(h))
    case T.Late{}:
      W.put_nat(3n, "")

# The stepper
# -----------

# the call, or a refused open
type St is Data:
  Call{c: T.C}
  Refused{}

def open.reply(r: T.C & T.Rec) -> St & String:
  (c, x) = r
  (Call{c}, put_rec(x))

def open.end(done: Bool, first: Bool) -> St & String:
  match done:
    case True{}:
      open.reply(T.open(first))
    case False{}:
      (Refused{}, W.err("tool_call: malformed open"))

def open.first(d: W.Dec<Bool>) -> St & String:
  match d:
    case W.Got{f, rest}:
      open.end(W.end(rest), f)
    case W.Bad{}:
      (Refused{}, W.err("tool_call: malformed open"))

# open: the call, a first attempt or a rerun as the input spells
def open(input: String) -> St & String:
  open.first(W.get_bool(input))

def fail() -> String:
  W.err("tool_call: malformed event")

def step.reply(r: T.C & T.Act) -> St & String:
  (c, a) = r
  (Call{c}, put_act(a))

def step.end(done: Bool, +c: T.C, e: T.Ev) -> St & String:
  match done:
    case True{}:
      step.reply(T.step(c, e))
    case False{}:
      (Call{c}, fail())

def step.ev(c: T.C, d: W.Dec<T.Ev>) -> St & String:
  match d:
    case W.Got{e, rest}:
      step.end(W.end(rest), c, e)
    case W.Bad{}:
      (Call{c}, fail())

# step: one event; the reply says what the Harness does
def step(st: St, input: String) -> St & String:
  match st:
    case Call{c}:
      step.ev(c, get_ev(input))
    case Refused{}:
      (Refused{}, W.err("tool_call: the open was refused"))

# The effect gate (a call)
# ------------------------

def get_replay.tag(n: Nat, s: String) -> W.Dec<T.Replay>:
  match n:
    case 0n:
      W.Got{T.Safe{}, s}
    case 1n:
      W.Got{T.Unsafe{}, s}
    case 2n+p:
      W.Bad{}

def get_replay.go(r: W.Dec<Nat>) -> W.Dec<T.Replay>:
  match r:
    case W.Got{n, s}:
      get_replay.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the replay policy at the start of s
def get_replay(s: String) -> W.Dec<T.Replay>:
  get_replay.go(W.get_nat(s))

def get_now.offered(r: W.Dec<T.Replay>) -> W.Dec<T.Now>:
  match r:
    case W.Got{p, s}:
      W.Got{T.Offered{p}, s}
    case W.Bad{}:
      W.Bad{}

def get_now.tag(n: Nat, s: String) -> W.Dec<T.Now>:
  match n:
    case 0n:
      W.Got{T.Gone{}, s}
    case 1n:
      get_now.offered(get_replay(s))
    case 2n+p:
      W.Bad{}

def get_now.go(r: W.Dec<Nat>) -> W.Dec<T.Now>:
  match r:
    case W.Got{n, s}:
      get_now.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the tool as resolved now, at the start of s
def get_now(s: String) -> W.Dec<T.Now>:
  get_now.go(W.get_nat(s))

def get_gate.enter(f: Bool, r: W.Dec<T.Now>) -> W.Dec<T.Gate>:
  match r:
    case W.Got{t, s}:
      W.Got{T.Enter{f, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_gate.recover(f: Bool, p: T.Replay, r: W.Dec<T.Now>) -> W.Dec<T.Gate>:
  match r:
    case W.Got{t, s}:
      W.Got{T.Recover{f, p, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_gate.stored(f: Bool, r: W.Dec<T.Replay>) -> W.Dec<T.Gate>:
  match r:
    case W.Got{p, s}:
      get_gate.recover(f, p, get_now(s))
    case W.Bad{}:
      W.Bad{}

def get_gate.intent(f: Bool, x: Bool, r: W.Dec<Bool>) -> W.Dec<T.Gate>:
  match r:
    case W.Got{i, s}:
      W.Got{T.Stop{f, x, i}, s}
    case W.Bad{}:
      W.Bad{}

def get_gate.restart(f: Bool, r: W.Dec<Bool>) -> W.Dec<T.Gate>:
  match r:
    case W.Got{x, s}:
      get_gate.intent(f, x, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_gate.found(n: Nat, r: W.Dec<Bool>) -> W.Dec<T.Gate>:
  match n:
    case 0n:
      match r:
        case W.Got{f, s}:
          get_gate.enter(f, get_now(s))
        case W.Bad{}:
          W.Bad{}
    case 1n:
      match r:
        case W.Got{f, s}:
          get_gate.stored(f, get_replay(s))
        case W.Bad{}:
          W.Bad{}
    case 2n:
      match r:
        case W.Got{f, s}:
          get_gate.restart(f, W.get_bool(s))
        case W.Bad{}:
          W.Bad{}
    case 3n+p:
      W.Bad{}

def get_gate.tag(n: Nat, s: String) -> W.Dec<T.Gate>:
  get_gate.found(n, W.get_bool(s))

def get_gate.go(r: W.Dec<Nat>) -> W.Dec<T.Gate>:
  match r:
    case W.Got{n, s}:
      get_gate.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the gate question at the start of s
def get_gate(s: String) -> W.Dec<T.Gate>:
  get_gate.go(W.get_nat(s))

def put_go(g: T.Go) -> String:
  match g:
    case T.Run{}:
      W.put_nat(0n, "")
    case T.Missing{}:
      W.put_nat(1n, "")
    case T.Unavailable{}:
      W.put_nat(2n, "")
    case T.Rerun{}:
      W.put_nat(3n, "")
    case T.Interrupted{}:
      W.put_nat(4n, "")
    case T.Aborted{}:
      W.put_nat(5n, "")
    case T.Abandoned{}:
      W.put_nat(6n, "")

def ffi.end(done: Bool, q: T.Gate) -> String:
  match done:
    case True{}:
      put_go(T.gate(q))
    case False{}:
      W.err("tool_call: malformed gate")

def ffi.gate(d: W.Dec<T.Gate>) -> String:
  match d:
    case W.Got{q, rest}:
      ffi.end(W.end(rest), q)
    case W.Bad{}:
      W.err("tool_call: malformed gate")

# ffi: the gate's answer to one question
def ffi(input: String) -> String:
  ffi.gate(get_gate(input))

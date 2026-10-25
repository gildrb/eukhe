# ffi_tool_call: the stepper of the compiled Bend core for one tool call's
# journal (crates/eukhe-durable/src/harness/tool/invocation.rs): its state
# is the call of bend/tool_call.bend, kept in the Bend heap. The Harness
# opens it where it journals the call's start, sends each report and the
# end of the tool's execute as they come, and does what each reply says.
# The codec is the wire format of bend/wire.bend (crates/eukhe-bend/WIRE.md):
#
#   open    first: Bool (a first attempt, not a rerun)   reply: Rec
#   step    Ev                                           reply: Act
#   Rec     0 began (the slot goes running), 1 cleared (a rerun clears it)
#   Ev      0 a report | 1 threw: Bool, aborted: Bool (the execute's end)
#   Act     0 keep | 1 refuse | 2 how (settle) | 3 late
#   How     0 finished, 1 failed, 2 cancelled
#
# A malformed event, or one with input left over, answers the error form
# and keeps the call; a malformed open opens the refused state, which
# answers every step with the error form. laws/tool_call.bend pins the
# entry. Pure: no IO, no @unsafe.

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

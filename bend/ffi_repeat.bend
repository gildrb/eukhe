import Base
import ./wire.bend as W
import ./repeat.bend as Rp

# ffi_repeat: the stepper of the compiled Bend core for the rounds in a
# row with the same tool calls and the same results (bend/repeat.bend).
# Its state, the walk, stays in the Bend heap: Rust
# (crates/eukhe-durable harness/generation/repeat.rs through
# `eukhe_bend::rules::repeat`) opens it with the requested calls' id and
# sends the context's messages newest first, one step each, until the
# row ends.
#
#   open   want: Nat (the requested calls' id)    reply: empty
#   step   a message, its tag then its field:     reply: 0 (the row goes on)
#            0 system, 1 user, 2 result (id: Nat),       | 1, count: Nat (it ended)
#            3 reply with calls (id: Nat),
#            4 reply with no call, 5 no older message
#
# An ended row stays ended: every later step answers the same count. A
# malformed message, or one with input left over, answers the error form
# "repeat: malformed message" and keeps the walk; an open with a
# malformed id opens the refused state, which answers every step with the
# error form "repeat: the open was refused". laws/repeat.bend (section
# entry) states this file's laws. Pure: no IO, no @unsafe.

# Encoding
# --------

# the row ended with count c
def put_stop(c: Nat) -> String:
  W.put_nat(1n, W.put_nat(c, ""))

# Decoding
# --------

def get_result(r: W.Dec<Nat>) -> W.Dec<Rp.Ev>:
  match r:
    case W.Got{x, s}:
      W.Got{Rp.Result{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_called(r: W.Dec<Nat>) -> W.Dec<Rp.Ev>:
  match r:
    case W.Got{x, s}:
      W.Got{Rp.Called{x}, s}
    case W.Bad{}:
      W.Bad{}

# a message: its tag, then its id for a result or a reply with calls
def get_ev(r: W.Dec<Nat>) -> W.Dec<Rp.Ev>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Rp.System{}, s}
        case 1n:
          W.Got{Rp.User{}, s}
        case 2n:
          get_result(W.get_nat(s))
        case 3n:
          get_called(W.get_nat(s))
        case 4n:
          W.Got{Rp.Said{}, s}
        case 5n:
          W.Got{Rp.End{}, s}
        case 6n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# The stepper
# -----------

# the walk, an ended row, or a refused open
type St is Data:
  Live{w: Rp.Walk}
  Ended{count: Nat}
  Shut{}

def open.end(whole: Bool, want: Nat) -> St & String:
  match whole:
    case True{}:
      (Live{Rp.start(want)}, "")
    case False{}:
      (Shut{}, W.err("repeat: malformed open"))

def open.go(d: W.Dec<Nat>) -> St & String:
  match d:
    case W.Got{want, s}:
      open.end(W.end(s), want)
    case W.Bad{}:
      (Shut{}, W.err("repeat: malformed open"))

# open: a walk of the requested calls' id that read no message yet
def open(input: String) -> St & String:
  open.go(W.get_nat(input))

def step.of(n: Rp.Next) -> St & String:
  match n:
    case Rp.Goes{w}:
      (Live{w}, W.put_nat(0n, ""))
    case Rp.Stops{+c}:
      (Ended{c}, put_stop(c))

def step.end(whole: Bool, w: Rp.Walk, e: Rp.Ev) -> St & String:
  match whole:
    case True{}:
      step.of(Rp.step(w, e))
    case False{}:
      (Live{w}, W.err("repeat: malformed message"))

def step.ev(w: Rp.Walk, d: W.Dec<Rp.Ev>) -> St & String:
  match d:
    case W.Got{e, s}:
      step.end(W.end(s), w, e)
    case W.Bad{}:
      (Live{w}, W.err("repeat: malformed message"))

# step: the next older message; the reply is whether the row ended
def step(st: St, input: String) -> St & String:
  match st:
    case Live{w}:
      step.ev(w, get_ev(W.get_nat(input)))
    case Ended{+c}:
      (Ended{c}, put_stop(c))
    case Shut{}:
      (Shut{}, W.err("repeat: the open was refused"))

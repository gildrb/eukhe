import Base
import ./wire.bend as W
import ./throttle.bend as Th

# ffi_throttle: the stepper of the compiled Bend core for the throttle of
# one streamed request's partials (bend/throttle.bend). Its state, the
# throttle's flags, stays in the Bend heap: Rust
# (crates/eukhe-durable harness/generation/stream.rs through
# `eukhe_bend::rules::throttle`) opens it, steps each event and does the
# actions the reply lists.
#
#   open   empty input                            reply: empty
#   step   an event, its tag then its field:      reply: List<Act>
#            0 a partial (has content: Bool),       Act = 0 keep the partial,
#            1 the timer fired, 2 the commit          1 arm the timer, 2 start a
#            settled, 3 stop, 4 dropped               commit of the pending
#                                                     partial, 3 abort the
#                                                     timer, 4 await the commit
#
# A malformed event, or one with input left over, answers the error form
# "throttle: malformed event" and keeps the throttle; an open with any
# input opens the refused state, which answers every step with the error
# form "throttle: the open was refused". laws/throttle.bend (section
# entry) states this file's laws. Pure: no IO, no @unsafe.

# Encoding
# --------

def put_act(a: Th.Act, rest: String) -> String:
  match a:
    case Th.Keep{}:
      W.put_nat(0n, rest)
    case Th.Arm{}:
      W.put_nat(1n, rest)
    case Th.Commit{}:
      W.put_nat(2n, rest)
    case Th.Abort{}:
      W.put_nat(3n, rest)
    case Th.Await{}:
      W.put_nat(4n, rest)

# Decoding
# --------

def get_part(r: W.Dec<Bool>) -> W.Dec<Th.Ev>:
  match r:
    case W.Got{b, s}:
      W.Got{Th.Part{b}, s}
    case W.Bad{}:
      W.Bad{}

# an event: its tag, then whether a partial has content
def get_ev(r: W.Dec<Nat>) -> W.Dec<Th.Ev>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_part(W.get_bool(s))
        case 1n:
          W.Got{Th.Fire{}, s}
        case 2n:
          W.Got{Th.Settle{}, s}
        case 3n:
          W.Got{Th.Finish{}, s}
        case 4n:
          W.Got{Th.Quit{}, s}
        case 5n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# The stepper
# -----------

# the throttle, or a refused open
type St is Data:
  Live{g: Th.Gate}
  Shut{}

# open: a throttle that saw nothing
def open(input: String) -> St & String:
  match input:
    case SNil{}:
      (Live{Th.start()}, "")
    case SCon{h, t}:
      (Shut{}, W.err("throttle: malformed open"))

def step.of(m: Th.Moved) -> St & String:
  match m:
    case Th.Moved{g, acts}:
      (Live{g}, W.put_list(~Th.Act, ~put_act, acts, ""))

def step.end(whole: Bool, g: Th.Gate, e: Th.Ev) -> St & String:
  match whole:
    case True{}:
      step.of(Th.step(g, e))
    case False{}:
      (Live{g}, W.err("throttle: malformed event"))

def step.ev(g: Th.Gate, d: W.Dec<Th.Ev>) -> St & String:
  match d:
    case W.Got{e, s}:
      step.end(W.end(s), g, e)
    case W.Bad{}:
      (Live{g}, W.err("throttle: malformed event"))

# step: one event; the reply is the host's actions
def step(st: St, input: String) -> St & String:
  match st:
    case Live{g}:
      step.ev(g, get_ev(W.get_nat(input)))
    case Shut{}:
      (Shut{}, W.err("throttle: the open was refused"))

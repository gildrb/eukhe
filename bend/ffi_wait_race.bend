# ffi_wait: the stepper of the compiled Bend core for eukhe's race
# (crates/eukhe-core/src/memory/service/race.rs): its state is the wait
# of bend/wait.bend, kept in the Bend heap. The race opens it with its
# deadline and sends what it finds ready at each poll; the stepper
# answers the ends the poll brings (`M.race`), and the race ends at the
# first. The codec is the wire format of bend/wire.bend
# (crates/eukhe-bend/WIRE.md):
#
#   open    the deadline in ticks: Maybe<Nat>     reply: Ends
#   step    work: Bool, cancel: Bool, late: Bool  reply: Ends
#           (the event is ready, the cancel fired, the deadline passed)
#   Ends    List<End>, End: 0 the event, 1 the deadline, 2 the cancel
#
# A malformed poll, or one with input left over, answers the error form
# and keeps the wait; a malformed open opens the refused state, which
# answers every step with the error form. laws/wait.bend (wait_entry_*)
# pins the entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./wait.bend as M

# Decoders
# --------

def get_ready.late(w: Bool, c: Bool, r: W.Dec<Bool>) -> W.Dec<M.Polled>:
  match r:
    case W.Got{l, s}:
      W.Got{M.Polled{w, c, l}, s}
    case W.Bad{}:
      W.Bad{}

def get_ready.cancel(w: Bool, r: W.Dec<Bool>) -> W.Dec<M.Polled>:
  match r:
    case W.Got{c, s}:
      get_ready.late(w, c, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ready.go(r: W.Dec<Bool>) -> W.Dec<M.Polled>:
  match r:
    case W.Got{w, s}:
      get_ready.cancel(w, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

# the poll at the start of s
def get_ready(s: String) -> W.Dec<M.Polled>:
  get_ready.go(W.get_bool(s))

def get_dl.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{d, s}:
      W.Got{Some{d}, s}
    case W.Bad{}:
      W.Bad{}

def get_dl.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_dl.some(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_dl.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_dl.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the deadline at the start of s
def get_dl(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_dl.go(W.get_nat(s))

# Encoder
# -------

def put_end(e: M.End, rest: String) -> String:
  match e:
    case M.Arrived{}:
      W.put_nat(0n, rest)
    case M.Expired{}:
      W.put_nat(1n, rest)
    case M.Cancelled{}:
      W.put_nat(2n, rest)

def put_ends(es: List<&2, M.End>) -> String:
  W.put_list(~M.End, ~put_end, es, "")

# The stepper
# -----------

# the wait, or a refused open
type St is Data:
  Live{w: M.W}
  Shut{}

def fail() -> String:
  W.err("wait: malformed poll")

def open.end(done: Bool, +dl: Maybe<&2, Nat>) -> St & String:
  match done:
    case True{}:
      (Live{M.start(dl)}, put_ends(M.first(dl)))
    case False{}:
      (Shut{}, W.err("wait: malformed open"))

def open.dl(d: W.Dec<Maybe<&2, Nat>>) -> St & String:
  match d:
    case W.Got{dl, rest}:
      open.end(W.end(rest), dl)
    case W.Bad{}:
      (Shut{}, W.err("wait: malformed open"))

# open: the wait with the deadline the input spells
def open(input: String) -> St & String:
  open.dl(get_dl(input))

def step.reply(r: M.W & List<&2, M.End>) -> St & String:
  (w, es) = r
  (Live{w}, put_ends(es))

def step.end(done: Bool, +w: M.W, r: M.Polled) -> St & String:
  match done:
    case True{}:
      step.reply(M.race(w, r))
    case False{}:
      (Live{w}, fail())

def step.poll(w: M.W, d: W.Dec<M.Polled>) -> St & String:
  match d:
    case W.Got{r, rest}:
      step.end(W.end(rest), w, r)
    case W.Bad{}:
      (Live{w}, fail())

# step: one poll; the reply holds the ends it brings
def step(st: St, input: String) -> St & String:
  match st:
    case Live{w}:
      step.poll(w, get_ready(input))
    case Shut{}:
      (Shut{}, W.err("wait: the open was refused"))

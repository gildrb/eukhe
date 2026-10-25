import Base
import ./wire.bend as W
import ./job.bend as M

# ffi_job_wait: the stepper of the compiled Bend core for one blocking
# wait on a job (bend/job.bend `wait`), run by the Rust wait
# (crates/eukhe-core/src/durable/jobs/mod.rs `wait_until`), which sends
# each event in the order it arrives and acts on the reply. Its state is
# the ticks of budget left, or the final turn. Each event's turn is the
# model's `poll`: due when no tick of budget is left after the event,
# ready when the event is the job's end. The codec is the wire format of
# bend/wire.bend (crates/eukhe-bend/WIRE.md):
#
#   open    budget: Nat (ticks)                     reply: Turn
#   step    Ev                                      reply: Turn
#   Ev      0 (a tick: the deadline timer fired) | 1 (the job's end came)
#   Turn    0 the call waits | 1 it settles with the end | 2 it detaches
#
# The end carries nothing: its value stays the host's. Once the call
# settles or detaches, every later event answers that turn. An open that
# is not exactly one Nat answers the error form "job_wait: malformed open"
# and opens the refused state, which answers every step with "job_wait:
# the open was refused"; a malformed event (an unknown tag, input left
# over) answers "job_wait: malformed event" and keeps the state.
# laws/job_wait.bend pins the entry. Pure: no IO, no @unsafe.

# the wait: waiting with left ticks of budget, or final
type Wt is Data:
  Waiting{left: Nat}
  Final{turn: M.Turn}

# the wait, or a refused open
type St is Data:
  Open{w: Wt}
  Shut{}

def put_turn(t: M.Turn) -> String:
  match t:
    case M.Waits{}:
      W.put_nat(0n, "")
    case M.Settles{}:
      W.put_nat(1n, "")
    case M.Detaches{}:
      W.put_nat(2n, "")

# the wait after the turn t, with left ticks of budget
def take(left: Nat, t: M.Turn) -> St & String:
  match t:
    case M.Waits{}:
      (Open{Waiting{left}}, W.put_nat(0n, ""))
    case M.Settles{}:
      (Open{Final{M.Settles{}}}, W.put_nat(1n, ""))
    case M.Detaches{}:
      (Open{Final{M.Detaches{}}}, W.put_nat(2n, ""))

def open.end(whole: Bool, +b: Nat) -> St & String:
  match whole:
    case True{}:
      take(b, M.poll(Nat.is_eq(b, 0n), False{}))
    case False{}:
      (Shut{}, W.err("job_wait: malformed open"))

def open.go(r: W.Dec<Nat>) -> St & String:
  match r:
    case W.Got{b, s}:
      open.end(W.end(s), b)
    case W.Bad{}:
      (Shut{}, W.err("job_wait: malformed open"))

# open: the wait with b ticks of budget, before any event
def open(input: String) -> St & String:
  open.go(W.get_nat(input))

# a tick spends one tick of budget
def tick(left: Nat) -> St & String:
  match left:
    case 0n:
      take(0n, M.poll(True{}, False{}))
    case 1n++l:
      take(l, M.poll(Nat.is_eq(l, 0n), False{}))

# the end spends none
def came(+left: Nat) -> St & String:
  take(left, M.poll(Nat.is_eq(left, 0n), True{}))

def step.wait(w: Wt, ready: Bool) -> St & String:
  match w:
    case Waiting{left}:
      match ready:
        case True{}:
          came(left)
        case False{}:
          tick(left)
    case Final{+t}:
      (Open{Final{t}}, put_turn(t))

def fail() -> String:
  W.err("job_wait: malformed event")

def step.tag(+w: Wt, t: Nat) -> St & String:
  match t:
    case 0n:
      step.wait(w, False{})
    case 1n:
      step.wait(w, True{})
    case 2n+p:
      (Open{w}, fail())

def step.end(whole: Bool, +w: Wt, t: Nat) -> St & String:
  match whole:
    case True{}:
      step.tag(w, t)
    case False{}:
      (Open{w}, fail())

def step.go(+w: Wt, r: W.Dec<Nat>) -> St & String:
  match r:
    case W.Got{t, s}:
      step.end(W.end(s), w, t)
    case W.Bad{}:
      (Open{w}, fail())

# step: one event; the reply is the call's turn
def step(st: St, input: String) -> St & String:
  match st:
    case Open{w}:
      step.go(w, W.get_nat(input))
    case Shut{}:
      (Shut{}, W.err("job_wait: the open was refused"))

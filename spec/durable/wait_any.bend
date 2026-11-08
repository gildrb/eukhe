# wait_any (spec): the agent's one blocking wait on its own work
# (`jobs.wait`), restated without the code (bend/wait_any.bend). The laws
# of area wait_any (laws/wait_any.bend) state the code's answers as
# properties of these terms. A spec: the shipped code never calls it.
#
# S1: a wait ends with the settled target of the lowest position. A ready
#     target (settled, its result undelivered) is settled; a gone one
#     (settled and delivered) only when the caller named the targets.
# S2: with no settled target: when no target runs, the wait is refused
#     (nothing to wait for); else the user's cancel ends it, else the cap
#     ends it, else it goes on.
# S3: a settled job's result goes to the session's notice exactly when no
#     wait watches it and the session has a wake path; otherwise a wait
#     (the one watching it, or a later one) takes it.
# S4: a wait lasts what the caller asked when that is within the cap of 30
#     minutes (1800 seconds), else the cap; the cap when the caller asked
#     nothing.
# S5: one job's delivery, event by event. A job runs, then is settled and
#     held for a wait (kept), or settled and delivered (sent). Watch adds
#     a watcher; unwatch removes one (none stays none); settles and taken
#     keep the watchers. A wait watches the job when it has a watcher
#     (w > 0), counted after the event. A settle of a running job, and an
#     unwatch of a kept one, place the result where S3 routes it: sent to
#     the notice, or kept. A take of a kept result sends it; every other
#     event keeps the phase (a sent result stays sent: it is never
#     delivered again). An event delivers the result exactly when it moves
#     the phase from not sent to sent: one delivery, else none.

import Base
import ../../bend/wait_any.bend as M

# S1: which targets count as settled
# ----------------------------------

# a target counts as settled (S1): a running one never, a ready one
# always, a gone one only for a wait that named its targets
def counts(+named: Bool, t: M.Tgt) -> Bool:
  match t:
    case M.Runs{}:
      False{}
    case M.Unread{}:
      True{}
    case M.Read{}:
      named

# no target of ts counts as settled
def none_settled(+named: Bool, ts: List<&2, M.Tgt>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, rest}:
      Bool.and(Bool.not(counts(named, t)), none_settled(named, rest))

# S2: the running targets
# -----------------------

def is_runs(t: M.Tgt) -> Bool:
  match t:
    case M.Runs{}:
      True{}
    case M.Unread{}:
      False{}
    case M.Read{}:
      False{}

# some target of ts runs
def some_runs(ts: List<&2, M.Tgt>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{t, rest}:
      Bool.or(is_runs(t), some_runs(rest))

# S3: the route
# -------------

def route.of(notice: Bool) -> M.Route:
  match notice:
    case True{}:
      M.ToNotice{}
    case False{}:
      M.ToWaiter{}

def route(watched: Bool, wake: Bool) -> M.Route:
  route.of(Bool.and(Bool.not(watched), wake))

# S4: the length
# --------------

def cap() -> Nat:
  1800n

def timeout.of(within: Bool, t: Nat) -> Nat:
  match within:
    case True{}:
      t
    case False{}:
      cap()

def timeout(asked: Maybe<&2, Nat>) -> Nat:
  match asked:
    case None{}:
      cap()
    case Some{+t}:
      timeout.of(Nat.is_le(t, cap()), t)

# S5: one job's delivery, read from a step's answer
# -------------------------------------------------

# the deliveries of a step's answer
def out_k(o: M.Out) -> Nat:
  match o:
    case M.Out{d, k}:
      k

# the state after a step's answer
def out_d(o: M.Out) -> M.D:
  match o:
    case M.Out{d, k}:
      d

# the watchers of a delivery state
def d_watchers(d: M.D) -> Nat:
  match d:
    case M.D{w, p}:
      w

# the phase of a delivery state
def d_phase(d: M.D) -> M.Phase:
  match d:
    case M.D{w, p}:
      p

# the watchers after a step
def out_watchers(o: M.Out) -> Nat:
  d_watchers(out_d(o))

# the phase after a step
def out_phase(o: M.Out) -> M.Phase:
  d_phase(out_d(o))

def is_sent(p: M.Phase) -> Bool:
  match p:
    case M.Live{}:
      False{}
    case M.Kept{}:
      False{}
    case M.Sent{}:
      True{}

def moved.of(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# the deliveries of a move from phase a to phase b: one exactly when it
# moves from not sent to sent
def moved(+a: M.Phase, +b: M.Phase) -> Nat:
  moved.of(Bool.and(Bool.not(is_sent(a)), is_sent(b)))

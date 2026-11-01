# wait_any (spec): the agent's one blocking wait on its own work
# (`jobs.wait`), restated without the code (bend/wait_any.bend). The laws
# of area wait_any (laws/wait_any.bend) state that the code refines it. A
# spec: the shipped code never calls it.
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

# S1: the settled target of the lowest position
# ---------------------------------------------

def counts(+named: Bool, t: M.Tgt) -> Bool:
  match t:
    case M.Runs{}:
      False{}
    case M.Unread{}:
      True{}
    case M.Read{}:
      named

def later(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{i}:
      Some{1n+i}

def pos.at(here: Bool, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match here:
    case True{}:
      Some{0n}
    case False{}:
      later(rest)

# the position of the first target of ts that counts as settled
def pos(ts: List<&2, M.Tgt>, +named: Bool) -> Maybe<&2, Nat>:
  match ts:
    case Nil{}:
      None{}
    case Con{t, rest}:
      pos.at(counts(named, t), pos(rest, named))

# S2: the running targets
# -----------------------

def runs(t: M.Tgt) -> Nat:
  match t:
    case M.Runs{}:
      1n
    case M.Unread{}:
      0n
    case M.Read{}:
      0n

# how many targets of ts run
def running(ts: List<&2, M.Tgt>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case Con{t, rest}:
      Nat.add(runs(t), running(rest))

def poll.rest(idle: Bool, cancel: Bool, late: Bool) -> M.Pick:
  match idle:
    case True{}:
      M.NoWork{}
    case False{}:
      match cancel:
        case True{}:
          M.Stopped{}
        case False{}:
          match late:
            case True{}:
              M.Capped{}
            case False{}:
              M.Waits{}

def poll.of(m: Maybe<&2, Nat>, idle: Bool, cancel: Bool, late: Bool) -> M.Pick:
  match m:
    case Some{i}:
      M.Takes{i}
    case None{}:
      poll.rest(idle, cancel, late)

# S1, S2: one poll
def poll(+named: Bool, cancel: Bool, late: Bool, +ts: List<&2, M.Tgt>) -> M.Pick:
  poll.of(pos(ts, named), Nat.is_eq(running(ts), 0n), cancel, late)

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

# S5: one job's delivery
# ----------------------

# a wait watches a job of w watchers when it has one
def watching(+w: Nat) -> Bool:
  Nat.is_gt(w, 0n)

# a job before any event: no watcher, running
def fresh() -> M.D:
  M.D{0n, M.Live{}}

# the watchers after event e
def watchers(+w: Nat, e: M.Ev) -> Nat:
  match e:
    case M.Watch{}:
      1n+w
    case M.Unwatch{}:
      Nat.sub(w, 1n)
    case M.Settles{}:
      w
    case M.Taken{}:
      w

# the phase of a result placed by the route r
def placed(r: M.Route) -> M.Phase:
  match r:
    case M.ToNotice{}:
      M.Sent{}
    case M.ToWaiter{}:
      M.Kept{}

# the phase after event e, from phase p, with w watchers after the event
def next(+wake: Bool, +w: Nat, e: M.Ev, p: M.Phase) -> M.Phase:
  match e:
    case M.Watch{}:
      p
    case M.Unwatch{}:
      match p:
        case M.Live{}:
          M.Live{}
        case M.Kept{}:
          placed(route(watching(w), wake))
        case M.Sent{}:
          M.Sent{}
    case M.Settles{}:
      match p:
        case M.Live{}:
          placed(route(watching(w), wake))
        case M.Kept{}:
          M.Kept{}
        case M.Sent{}:
          M.Sent{}
    case M.Taken{}:
      match p:
        case M.Live{}:
          M.Live{}
        case M.Kept{}:
          M.Sent{}
        case M.Sent{}:
          M.Sent{}

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

# a running job's result placed by the route r, with w watchers
def deliver(r: M.Route, +w: Nat) -> M.Out:
  +p = placed(r)
  M.Out{M.D{w, p}, moved(M.Live{}, p)}

def step.at(+wake: Bool, +w: Nat, +p: M.Phase, +e: M.Ev) -> M.Out:
  +p2 = next(wake, w, e, p)
  M.Out{M.D{w, p2}, moved(p, p2)}

# one event: the job's delivery state after it, and the deliveries it made
def step(+wake: Bool, d: M.D, +e: M.Ev) -> M.Out:
  match d:
    case M.D{+w, +p}:
      step.at(wake, watchers(w, e), p, e)

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

# every delivery the events es make from d
def deliveries(es: List<&2, M.Ev>, +wake: Bool, d: M.D) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, rest}:
      +o = step(wake, d, e)
      Nat.add(out_k(o), deliveries(rest, wake, out_d(o)))

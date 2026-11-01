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

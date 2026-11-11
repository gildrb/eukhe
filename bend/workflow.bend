# workflow: the rules the compiled core decides for a dynamic workflow
# run (crates/eukhe-core/src/durable/workflow): the whole admission of one
# `agent()` call (`admit` in globals.rs), against the agent budget and the
# rows of the earlier run a resumed run takes answers from, and the limits
# a run works under (`effective_limits` in size.rs). The concurrency
# semaphore and the per-agent results of `parallel` and `pipeline` run in
# the script prelude (prelude.js), not here.
#
# The budget is two Nats: the agents spawned and the agents left. A spawn
# moves one unit from left to spawned; with none left the call is refused.

import Base

type Pool is Data:
  Pool{taken: Nat, left: Nat}

# Take one unit when one is left; else the pool stays (the call is
# refused).
def take(p: Pool) -> Pool:
  match p:
    case Pool{t, l}:
      match l:
        case 0n:
          Pool{t, 0n}
        case 1n+m:
          Pool{1n+t, m}

# Whether `take` would take a unit.
def can_take(p: Pool) -> Bool:
  match p:
    case Pool{t, l}:
      match l:
        case 0n:
          False{}
        case 1n+m:
          True{}

# The admission of one agent call
# -------------------------------

# The status of an agent's row (WorkflowAgentStatus): queued, running,
# done (`Finished`), failed (`Erred`), cancelled, or served from an earlier run's
# answer (`Cached`).
type Sts is Data:
  Queued{}
  Running{}
  Finished{}
  Erred{}
  Cancelled{}
  Cached{}

# A row of the run a resumed run takes answers from: its resume key and
# its status, in ordinal order.
type Row is Data:
  Row{key: Nat, s: Sts}

# What one `agent()` call does: its ordinal ended in this run (the call
# replays the answer), its ordinal runs in this run (the call reattaches),
# the earlier run's row i serves it, it spawns an agent, or the budget
# refuses it.
type Admit is Data:
  Ended{}
  Reattach{}
  Reuse{i: Nat}
  Spawn{}
  Refused{}

# a row of status s holds a finished answer
def serves(s: Sts) -> Bool:
  match s:
    case Queued{}:
      False{}
    case Running{}:
      False{}
    case Finished{}:
      True{}
    case Erred{}:
      False{}
    case Cancelled{}:
      False{}
    case Cached{}:
      True{}

# what a call does with its ordinal's row of status s in this run
def again(s: Sts) -> Admit:
  match s:
    case Queued{}:
      Reattach{}
    case Running{}:
      Reattach{}
    case Finished{}:
      Ended{}
    case Erred{}:
      Ended{}
    case Cancelled{}:
      Ended{}
    case Cached{}:
      Ended{}

def found.at(hit: Bool, i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      rest

# the index of the first row of rs, counted from i, with key k and a
# finished answer
def found(rs: List<&2, Row>, +k: Nat, i: Nat) -> Maybe<&2, Nat>:
  match rs:
    case Nil{}:
      None{}
    case Row{key, s} <> rest:
      +j = i
      found.at(Bool.and(Nat.is_eq(k, key), serves(s)), j, found(rest, k, 1n+j))

def admit.take(ok: Bool, p: Pool) -> Admit & Pool:
  match ok:
    case True{}:
      (Spawn{}, take(p))
    case False{}:
      (Refused{}, p)

def admit.fresh(hit: Maybe<&2, Nat>, +p: Pool) -> Admit & Pool:
  match hit:
    case Some{i}:
      (Reuse{i}, p)
    case None{}:
      admit.take(can_take(p), p)

# One call: its ordinal's row in this run (none for a new ordinal), its
# key, the earlier run's rows (none for a fresh run), and the budget (the
# agents spawned and the agents left).
def admit(prior: Maybe<&2, Sts>, +k: Nat, rs: List<&2, Row>, p: Pool) -> Admit & Pool:
  match prior:
    case Some{s}:
      (again(s), p)
    case None{}:
      admit.fresh(found(rs, k, 0n), p)

# The limits of a run
# -------------------

# A run's concurrency and max agents.
type Limits is Data:
  Limits{conc: Nat, max: Nat}

def capped(le: Bool, c: Nat, cap: Nat) -> Nat:
  match le:
    case True{}:
      c
    case False{}:
      cap

# the limits l of a run's size under the subagent cap (0: no cap): the
# concurrency at most the cap, the max agents as they are
def effective(l: Limits, cap: Nat) -> Limits:
  match l:
    case Limits{+c, m}:
      match cap:
        case 0n:
          Limits{c, m}
        case 1n++x:
          Limits{capped(Nat.is_le(c, 1n+x), c, 1n+x), m}

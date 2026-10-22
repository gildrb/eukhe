# workflow: the scheduler of a dynamic workflow run
# (crates/eukhe-core/src/durable/workflow): the concurrency semaphore of
# the script prelude, the agent budget and the resume cache, the whole
# admission of one `agent()` call (`admit` in globals.rs), the limits a
# run works under (`effective_limits` in size.rs), and the per-agent
# results of `parallel` and `pipeline`.
#
# A counter is two Nats: what is taken and what is left. An admission
# moves one unit from left to taken, a release moves it back; with none
# left the call waits (the semaphore) or is refused (the budget).

import Base

type Pool is Data:
  Pool{taken: Nat, left: Nat}

# A pool of `cap` units, none taken.
def pool(cap: Nat) -> Pool:
  Pool{0n, cap}

# Take one unit when one is left; else the pool stays (the call waits
# or is refused).
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

# Give one taken unit back (an agent settled).
def give(p: Pool) -> Pool:
  match p:
    case Pool{t, l}:
      match t:
        case 0n:
          Pool{0n, l}
        case 1n+s:
          Pool{s, 1n+l}

# An event of the semaphore: an agent asks for a slot, or one settles.
type Ev is Data:
  Ask{}
  Settle{}

def step(e: Ev, p: Pool) -> Pool:
  match e:
    case Ask{}:
      take(p)
    case Settle{}:
      give(p)

def run(es: List<&2, Ev>, p: Pool) -> Pool:
  match es:
    case Nil{}:
      p
    case e <> rest:
      run(rest, step(e, p))

# The units a pool holds in all.
def size(p: Pool) -> Nat:
  match p:
    case Pool{t, l}:
      Nat.add(t, l)

def taken(p: Pool) -> Nat:
  match p:
    case Pool{t, l}:
      t

# The budget: a run of `max` agents; a spawn takes one unit for good.
def spawns(n: Nat, p: Pool) -> Pool:
  match n:
    case 0n:
      p
    case 1n+m:
      spawns(m, take(p))

# The resume cache
# ----------------

def member(+k: Nat, cache: List<&2, Nat>) -> Bool:
  match cache:
    case Nil{}:
      False{}
    case c <> rest:
      Bool.or(Nat.is_eq(k, c), member(k, rest))

def cost.go(hit: Bool) -> Nat:
  match hit:
    case True{}:
      0n
    case False{}:
      1n

# the agents one call of a resumed run spawns: none for a key the earlier
# run finished, one for another key
def cost(+k: Nat, cache: List<&2, Nat>) -> Nat:
  cost.go(member(k, cache))

# The agents a resumed run spawns for its keys.
def resumed(+cache: List<&2, Nat>, keys: List<&2, Nat>) -> Nat:
  match keys:
    case Nil{}:
      0n
    case k <> rest:
      Nat.add(cost(k, cache), resumed(cache, rest))

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

# Results
# -------

# How one agent ended: an answer, or a failure.
type Out is Data:
  Answer{n: Nat}
  Failed{}

# What the script gets for one agent: the answer, or null.
def result(o: Out) -> Maybe<&2, Nat>:
  match o:
    case Answer{n}:
      Some{n}
    case Failed{}:
      None{}

# `parallel` and `pipeline`: every item's result, in item order.
def results(os: List<&2, Out>) -> List<&2, Maybe<&2, Nat>>:
  match os:
    case Nil{}:
      Nil{}
    case o <> rest:
      result(o) <> results(rest)

def cat(xs: List<&2, Out>, ys: List<&2, Out>) -> List<&2, Out>:
  match xs:
    case Nil{}:
      ys
    case x <> rest:
      x <> cat(rest, ys)

def rcat(xs: List<&2, Maybe<&2, Nat>>, ys: List<&2, Maybe<&2, Nat>>) -> List<&2, Maybe<&2, Nat>>:
  match xs:
    case Nil{}:
      ys
    case x <> rest:
      x <> rcat(rest, ys)

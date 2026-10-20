# workflow: the scheduler of a dynamic workflow run
# (crates/eukhe-core/src/durable/workflow): the concurrency semaphore of
# the script prelude, the agent budget and the resume cache of `admit`
# (globals.rs), and the per-agent results of `parallel` and `pipeline`.
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

# What one agent call of a resumed run does: a cached key spawns
# nothing, another key spawns one agent.
type Call is Data:
  Cached{}
  Spawn{}
  Refused{}

def cost.go(hit: Bool) -> Nat:
  match hit:
    case True{}:
      0n
    case False{}:
      1n

def cost(+k: Nat, cache: List<&2, Nat>) -> Nat:
  cost.go(member(k, cache))

# The agents a resumed run spawns for its keys.
def resumed(+cache: List<&2, Nat>, keys: List<&2, Nat>) -> Nat:
  match keys:
    case Nil{}:
      0n
    case k <> rest:
      Nat.add(cost(k, cache), resumed(cache, rest))

# One call against the cache and the budget (`admit` in globals.rs).
def call.take(ok: Bool, p: Pool) -> Call & Pool:
  match ok:
    case True{}:
      (Spawn{}, take(p))
    case False{}:
      (Refused{}, p)

def call.go(hit: Bool, +p: Pool) -> Call & Pool:
  match hit:
    case True{}:
      (Cached{}, p)
    case False{}:
      call.take(can_take(p), p)

def call(+k: Nat, cache: List<&2, Nat>, p: Pool) -> Call & Pool:
  call.go(member(k, cache), p)

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

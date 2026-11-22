# account: the account of one provider a run goes on with (Rust: eukhe-core
# durable/models/accounts.rs, asked by the provider runtime,
# durable/models/provider.rs, when a session first sends to a provider
# and when a request's account hits a usage limit or its login cannot
# refresh). The accounts are the provider's stored logins in their order
# (the order of `/accounts`); each has a mark:
#
#   - Free{}: usable;
#   - Until{t}: its usage limit holds until `t` (epoch ms): usable once
#     t <= now;
#   - Dead{}: its login cannot refresh.
#
# The run goes on with the first usable account. With none usable, the
# earliest limit to reset decides (the first such account on a tie): when
# it resets within the run's wait limit (`cap` ms from `now`) and the run
# may still wait (`waits` > 0), the run waits for it; else every account
# is limited past the wait, and the run goes to its model fallback with
# that reset. With no account limited and none usable, no login is left.
# Pure: no IO, no @unsafe.

import Base

# the state of one account
type Mark is Data:
  Free{}
  Until{t: Nat}
  Dead{}

# one decision: the clock, the wait limit, the waits left, the marks in
# order
type In is Data:
  In{now: Nat, cap: Nat, waits: Nat, marks: List<&2, Mark>}

# what the run does
type Choice is Data:
  Use{a: Nat}
  Hold{a: Nat, until: Nat}
  Quota{a: Nat, until: Nat}
  Login{}

# the earliest limit: its account and its reset
type Soon is Data:
  Soon{a: Nat, t: Nat}

# the account is usable at now
def free(+now: Nat, m: Mark) -> Bool:
  match m:
    case Free{}:
      True{}
    case Until{t}:
      Nat.is_le(t, now)
    case Dead{}:
      False{}

def first.of(hit: Bool, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{0n}
    case False{}:
      match rest:
        case None{}:
          None{}
        case Some{a}:
          Some{1n+a}

# the place of the first usable account
def first(+now: Nat, ms: List<&2, Mark>) -> Maybe<&2, Nat>:
  match ms:
    case Nil{}:
      None{}
    case m <> t:
      first.of(free(now, m), first(now, t))

# the earliest limit of the accounts after this one, one place further on
def later(r: Maybe<&2, Soon>) -> Maybe<&2, Soon>:
  match r:
    case None{}:
      None{}
    case Some{s}:
      match s:
        case Soon{a, t}:
          Some{Soon{1n+a, t}}

def soonest.pick(first: Bool, +u: Nat, +a: Nat, +t: Nat) -> Maybe<&2, Soon>:
  match first:
    case True{}:
      Some{Soon{0n, u}}
    case False{}:
      Some{Soon{1n+a, t}}

def soonest.until(+u: Nat, r: Maybe<&2, Soon>) -> Maybe<&2, Soon>:
  match r:
    case None{}:
      Some{Soon{0n, u}}
    case Some{s}:
      match s:
        case Soon{+a, +t}:
          soonest.pick(Nat.is_le(u, t), u, a, t)

def soonest.of(m: Mark, r: Maybe<&2, Soon>) -> Maybe<&2, Soon>:
  match m:
    case Free{}:
      later(r)
    case Until{u}:
      soonest.until(u, r)
    case Dead{}:
      later(r)

# the earliest limit: the place of its account (the first on a tie) and
# its reset
def soonest(ms: List<&2, Mark>) -> Maybe<&2, Soon>:
  match ms:
    case Nil{}:
      None{}
    case m <> t:
      soonest.of(m, soonest(t))

# the reset is within the wait limit and the run may still wait
def waits_for(+now: Nat, +cap: Nat, waits: Nat, t: Nat) -> Bool:
  match waits:
    case 0n:
      False{}
    case 1n+w:
      Nat.is_le(t, Nat.add(now, cap))

def limited.of(go: Bool, +a: Nat, +t: Nat) -> Choice:
  match go:
    case True{}:
      Hold{a, t}
    case False{}:
      Quota{a, t}

# no account usable: wait for the earliest limit, else hand it on
def limited(+now: Nat, +cap: Nat, waits: Nat, r: Maybe<&2, Soon>) -> Choice:
  match r:
    case None{}:
      Login{}
    case Some{s}:
      match s:
        case Soon{+a, +t}:
          limited.of(waits_for(now, cap, waits, t), a, t)

def choose.of(+now: Nat, +cap: Nat, waits: Nat, ms: List<&2, Mark>, f: Maybe<&2, Nat>) -> Choice:
  match f:
    case Some{a}:
      Use{a}
    case None{}:
      limited(now, cap, waits, soonest(ms))

# the account the run goes on with
def choose(x: In) -> Choice:
  match x:
    case In{+now, +cap, waits, +ms}:
      choose.of(now, cap, waits, ms, first(now, ms))

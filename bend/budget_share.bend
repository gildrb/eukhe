# budget_share: the offer a reservation of an agent that shares its account
# starts from (Rust: eukhe-bend rules/budget.rs share_start, asked before a
# reservation of an agent that draws from a shared account). Run as the
# compiled core by bend/ffi_budget_share.bend.
#
# Every agent of a task tree without a budget of its own draws from one
# account (bend/budget.bend), and a reservation grants the first of its
# offers that fits: the first of several agents working at once would hold
# the largest offer that fits and leave its siblings nothing. So a work or
# side request starts from the first offer that fits and is within its
# share: in money and in tokens, at most what is free past the reserves
# (base, and the agent's own keep) divided by the number of the account's
# Working agents that hold nothing (n, the asker among them: at least 1).
# When no offer that fits is within the share it starts from the smallest
# offer that fits (the last that fits); when none fits, from the wanted
# one (place 0). A final answer is not shared: it starts from the first
# offer that fits. Tool calls, model requests and time are not shared: the
# fit covers them. The caller reserves the offers from that place on
# (budget.bend reserve, unchanged), so a request is refused exactly when it
# would be from the wanted one, and the hold settles to the actual spend.
# Pure: no IO, no @unsafe.

import Base
import ./budget.bend as B

# Fitting
# -------

def fits.of(l: Maybe<&2, B.Dim>) -> Bool:
  match l:
    case None{}:
      True{}
    case Some{d}:
      False{}

# the offer c fits what is free by the deadline, with the reserves
# (budget.bend need, lack: as reserve tests it)
def fits(use: B.Use, base: B.Ask, keep: B.Ask, c: B.Ask, free: B.Amt, now: Nat, until: Nat) -> Bool:
  fits.of(B.lack(B.need(use, base, keep, c), free, now, until))

# The share
# ---------

# the agents a share is divided among: n, at least the asker
def agents(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      1n+p

def amt.of(x: B.Ask) -> B.Amt:
  match x:
    case B.Ask{a, m}:
      a

# x is within a k-th of r, in money and in tokens
def share.le(+k: Nat, x: B.Amt, r: B.Amt) -> Bool:
  match x r:
    case B.Amt{xc, xk, xn, xr} B.Amt{rc, rk, rn, rr}:
      Bool.and(Nat.is_le(xc, Nat.div(rc, k)), Nat.is_le(xk, Nat.div(rk, k)))

# the offer c is within the share of n agents: what is free past the
# reserves (what an ask of nothing needs) divided by them
def share(n: Nat, use: B.Use, base: B.Ask, keep: B.Ask, c: B.Ask, free: B.Amt) -> Bool:
  share.le(agents(n), amt.of(c), B.sub4(free, amt.of(B.need(use, base, keep, B.Ask{B.zero(), 0n}))))

# work and a side request are shared; a final answer is not
def within(n: Nat, use: B.Use, base: B.Ask, keep: B.Ask, c: B.Ask, free: B.Amt) -> Bool:
  match use:
    case B.Work{}:
      share(n, B.Work{}, base, keep, c, free)
    case B.Final{}:
      True{}
    case B.Side{}:
      share(n, B.Side{}, base, keep, c, free)

# the offer c fits and is within the share
def ok(n: Nat, +use: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +free: B.Amt, now: Nat, until: Nat) -> Bool:
  Bool.and(fits(use, base, keep, c, free, now, until), within(n, use, base, keep, c, free))

# The start
# ---------

def next(r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match r:
    case None{}:
      None{}
    case Some{j}:
      Some{1n+j}

def first.or(b: Bool, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{0n}
    case False{}:
      next(r)

# the place of the first of xs that fits and is within the share
def first(xs: List<&2, B.Ask>, +n: Nat, +use: B.Use, +base: B.Ask, +keep: B.Ask, +free: B.Amt, +now: Nat, +until: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{c, t}:
      first.or(ok(n, use, base, keep, c, free, now, until), first(t, n, use, base, keep, free, now, until))

def last.or(r: Maybe<&2, Nat>, b: Bool) -> Maybe<&2, Nat>:
  match r:
    case Some{j}:
      Some{1n+j}
    case None{}:
      match b:
        case True{}:
          Some{0n}
        case False{}:
          None{}

# the place of the last of xs that fits
def last(xs: List<&2, B.Ask>, +use: B.Use, +base: B.Ask, +keep: B.Ask, +free: B.Amt, +now: Nat, +until: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{c, t}:
      last.or(last(t, use, base, keep, free, now, until), fits(use, base, keep, c, free, now, until))

def start.pick(f: Maybe<&2, Nat>, l: Maybe<&2, Nat>) -> Nat:
  match f:
    case Some{j}:
      j
    case None{}:
      match l:
        case Some{j}:
          j
        case None{}:
          0n

# the place among want and then less of the offer the reservation of an
# agent sharing its account with n agents starts from: the first that fits
# and is within the share, else the last that fits, else 0
def start(n: Nat, +use: B.Use, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +free: B.Amt, +now: Nat, +until: Nat) -> Nat:
  start.pick(first(want <> less, n, use, base, keep, free, now, until), last(want <> less, use, base, keep, free, now, until))

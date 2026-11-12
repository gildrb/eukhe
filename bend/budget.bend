# budget: the ledger of a task tree's budget (Rust: eukhe-budget
# ledger.rs, asked before every provider request, tool call and child
# spawn, and after each of them). Run as the compiled core by
# bend/ffi_budget.bend (eukhe-bend rules/budget.rs).
#
# A budget limits money (cost), tokens, tool calls and model requests,
# which are spent, and wall-clock time, which is a deadline (`until`) for
# the whole tree.
# An account holds, per spent dimension, what is free, what is spent,
# what is lent to children given their own budget and what was spent past
# the funding (an overrun: a provider that reported more than its
# reservation), next to the open reservations (holds) and its deadline.
# Every agent of the tree that has no budget of its own draws from the
# same account; each agent has its own phase.
#
# An ask is an amount and a duration in milliseconds.
#
# reserve: before anything is spent, its worst case is taken out of free
#   and held under an id, and it must end before the deadline. The caller
#   offers asks in order (the wanted one, then smaller ones: a reduced
#   output cap, a shorter timeout); the first that fits is granted. Every
#   reservation leaves `base` free and ends `base` before the deadline
#   (the final-answer reserves of the agents above the asking one); work
#   and a side request (a request of the agent that is not its own turn:
#   a title, a classifier, a compaction, a memory or side question) must
#   also leave `keep` (the worst case of its own final answer). No offer
#   fits: nothing is held, work moves the agent to WrapUp (only a final
#   answer and side requests are admitted from then on), a final answer
#   moves it to Exhausted (nothing is admitted) and a side request leaves
#   the phase as it was.
# settle: the actual spend replaces the hold; what was not spent is free
#   again. An id that is not held changes nothing.
# carve: a child given its own budget: the allotment leaves the parent's
#   free and is lent; the child's deadline is its own duration from now.
# close: an idle child's free returns, its spend becomes the parent's.
# fund: more budget and more time; an overrun is repaid first.
# Pure: no IO, no @unsafe.

import Base

# An amount in each spent dimension: money, tokens, tool calls, model
# requests
type Amt is Data:
  Amt{cost: Nat, tok: Nat, calls: Nat, reqs: Nat}

# A dimension of a budget
type Dim is Data:
  Cost{}
  Tok{}
  Time{}
  Calls{}
  Reqs{}

# What a reservation asks for: an amount and how long it may run
type Ask is Data:
  Ask{amt: Amt, ms: Nat}

# An open reservation
type Hold is Data:
  Hold{id: Nat, amt: Amt}

# What an agent is admitted: work and a final answer, a final answer only,
# nothing
type Phase is Data:
  Working{}
  WrapUp{}
  Exhausted{}

# The ledger of one account: what is free, spent, lent and overrun, the
# open holds, the deadline
type Acct is Data:
  Acct{free: Amt, spent: Amt, lent: Amt, over: Amt, holds: List<&2, Hold>, until: Nat}

# What a reservation is for: work (must leave the final-answer reserve),
# the final answer itself, or a side request: a request of the agent that
# is not its own turn (a title, a classifier, a compaction, a memory or
# side question), which leaves the final-answer reserve like work
type Use is Data:
  Work{}
  Final{}
  Side{}

# Why nothing was taken: a dimension is short, the id is already held,
# the agent's phase does not admit it
type Why is Data:
  Short{dim: Dim}
  Held{}
  Stopped{}

# The answer to a reservation: the granted offer, its place and the
# account after it; or why not and the agent's phase after it
type Grant is Data:
  Granted{index: Nat, ask: Ask, acct: Acct, tight: Bool}
  Refused{why: Why, phase: Phase}

# The answer to a carve
type Carve is Data:
  Carved{parent: Acct, child: Acct}
  Kept{why: Why}

# The answer to a close
type Close is Data:
  Closed{parent: Acct, child: Acct}
  Busy{}

# Amounts
# -------

def zero() -> Amt:
  Amt{0n, 0n, 0n, 0n}

def add4(a: Amt, b: Amt) -> Amt:
  match a b:
    case Amt{ac, ak, an, ar} Amt{bc, bk, bn, br}:
      Amt{Nat.add(ac, bc), Nat.add(ak, bk), Nat.add(an, bn), Nat.add(ar, br)}

# a less b in each dimension, never below zero
def sub4(a: Amt, b: Amt) -> Amt:
  match a b:
    case Amt{ac, ak, an, ar} Amt{bc, bk, bn, br}:
      Amt{Nat.sub(ac, bc), Nat.sub(ak, bk), Nat.sub(an, bn), Nat.sub(ar, br)}

def is_zero4(a: Amt) -> Bool:
  match a:
    case Amt{c, k, n, r}:
      Bool.and(Nat.is_eq(c, 0n), Bool.and(Nat.is_eq(k, 0n), Bool.and(Nat.is_eq(n, 0n), Nat.is_eq(r, 0n))))

# Fitting
# -------

# both asks together
def plus(a: Ask, b: Ask) -> Ask:
  match a b:
    case Ask{ax, am} Ask{bx, bm}:
      Ask{add4(ax, bx), Nat.add(am, bm)}

# what an ask of c must find: the reserves above (base) and, for work and
# a side request, its own final-answer reserve (keep)
def need(use: Use, base: Ask, keep: Ask, c: Ask) -> Ask:
  match use:
    case Work{}:
      plus(plus(c, base), keep)
    case Final{}:
      plus(c, base)
    case Side{}:
      plus(plus(c, base), keep)

def lack.at(ok: Bool, d: Dim, rest: Maybe<&2, Dim>) -> Maybe<&2, Dim>:
  match ok:
    case True{}:
      rest
    case False{}:
      Some{d}

# the first dimension in which n is more than what is free, or (time)
# runs past the deadline from now, if any
def lack(n: Ask, f: Amt, now: Nat, until: Nat) -> Maybe<&2, Dim>:
  match n:
    case Ask{x, nm}:
      match x f:
        case Amt{nc, nk, nn, nr} Amt{fc, fk, fn, fr}:
          lack.at(Nat.is_le(nc, fc), Cost{}, lack.at(Nat.is_le(nk, fk), Tok{}, lack.at(Nat.is_le(Nat.add(now, nm), until), Time{}, lack.at(Nat.is_le(nn, fn), Calls{}, lack.at(Nat.is_le(nr, fr), Reqs{}, None{})))))

# The choice among the offers: the first that fits and its place, or the
# dimension the last one lacks
type Pick is Data:
  Fit{index: Nat, ask: Ask}
  NoFit{dim: Dim}

def pick.one(l: Maybe<&2, Dim>, i: Nat, c: Ask) -> Pick:
  match l:
    case None{}:
      Fit{i, c}
    case Some{d}:
      NoFit{d}

def pick.or(l: Maybe<&2, Dim>, i: Nat, c: Ask, rest: Pick) -> Pick:
  match l:
    case None{}:
      Fit{i, c}
    case Some{d}:
      rest

# the first of c (at place i) and then less that fits free by the
# deadline
def pick(less: List<&2, Ask>, +use: Use, +base: Ask, +keep: Ask, +free: Amt, +now: Nat, +until: Nat, +c: Ask, +i: Nat) -> Pick:
  match less:
    case Nil{}:
      pick.one(lack(need(use, base, keep, c), free, now, until), i, c)
    case Con{h, t}:
      pick.or(lack(need(use, base, keep, c), free, now, until), i, c, pick(t, use, base, keep, free, now, until, h, 1n+i))

# Holds
# -----

def held.is(same: Bool, rest: Bool) -> Bool:
  match same:
    case True{}:
      True{}
    case False{}:
      rest

# a hold of hs has the id
def held(+id: Nat, hs: List<&2, Hold>) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case Con{h, t}:
      match h:
        case Hold{hid, amt}:
          held.is(Nat.is_eq(hid, id), held(id, t))

def owed.add(same: Bool, amt: Amt, rest: Amt) -> Amt:
  match same:
    case True{}:
      add4(amt, rest)
    case False{}:
      rest

# what the holds of the id add up to
def owed(+id: Nat, hs: List<&2, Hold>) -> Amt:
  match hs:
    case Nil{}:
      zero()
    case Con{h, t}:
      match h:
        case Hold{hid, amt}:
          owed.add(Nat.is_eq(hid, id), amt, owed(id, t))

def others.keep(same: Bool, h: Hold, rest: List<&2, Hold>) -> List<&2, Hold>:
  match same:
    case True{}:
      rest
    case False{}:
      h <> rest

# the holds of every other id, in order
def others(+id: Nat, hs: List<&2, Hold>) -> List<&2, Hold>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      match h:
        case Hold{hid, amt}:
          others.keep(Nat.is_eq(hid, id), h, others(id, t))

# Reserve
# -------

# the phase admits the use: Working admits all, WrapUp the final answer
# and side requests, Exhausted nothing
def allows(p: Phase, k: Use) -> Bool:
  match p:
    case Working{}:
      True{}
    case WrapUp{}:
      match k:
        case Work{}:
          False{}
        case Final{}:
          True{}
        case Side{}:
          True{}
    case Exhausted{}:
      False{}

# the phase after no offer fit, of an agent in phase p: work wraps up, a
# final answer exhausts, a side request leaves p
def after(k: Use, p: Phase) -> Phase:
  match k:
    case Work{}:
      WrapUp{}
    case Final{}:
      Exhausted{}
    case Side{}:
      p

def tight.of(l: Maybe<&2, Dim>) -> Bool:
  match l:
    case None{}:
      False{}
    case Some{d}:
      True{}

def reserve.pick(p: Pick, +use: Use, phase: Phase, +id: Nat, +now: Nat, +base: Ask, +keep: Ask, +free: Amt, spent: Amt, lent: Amt, over: Amt, holds: List<&2, Hold>, +until: Nat) -> Grant:
  match p:
    case Fit{i, +c}:
      match c:
        case Ask{+x, +m}:
          +left = sub4(free, x)
          Granted{i, Ask{x, m}, Acct{left, spent, lent, over, Hold{id, x} <> holds, until}, tight.of(lack(need(use, base, keep, Ask{x, m}), left, Nat.add(now, m), until))}
    case NoFit{d}:
      Refused{Short{d}, after(use, phase)}

def reserve.held(h: Bool, +use: Use, phase: Phase, +id: Nat, +now: Nat, +base: Ask, +keep: Ask, +want: Ask, less: List<&2, Ask>, +free: Amt, spent: Amt, lent: Amt, over: Amt, holds: List<&2, Hold>, +until: Nat) -> Grant:
  match h:
    case True{}:
      Refused{Held{}, phase}
    case False{}:
      reserve.pick(pick(less, use, base, keep, free, now, until, want, 0n), use, phase, id, now, base, keep, free, spent, lent, over, holds, until)

def reserve.open(ok: Bool, +use: Use, phase: Phase, +id: Nat, +now: Nat, +base: Ask, +keep: Ask, +want: Ask, less: List<&2, Ask>, +free: Amt, spent: Amt, lent: Amt, over: Amt, +holds: List<&2, Hold>, +until: Nat) -> Grant:
  match ok:
    case True{}:
      reserve.held(held(id, holds), use, phase, id, now, base, keep, want, less, free, spent, lent, over, holds, until)
    case False{}:
      Refused{Stopped{}, phase}

# the reservation, by an agent in phase `phase` at time `now`, of the
# first of want and then less that fits, under id. Refusal order: the
# phase, an id already held, no offer fits.
def reserve(+use: Use, +phase: Phase, +id: Nat, +now: Nat, +base: Ask, +keep: Ask, +want: Ask, less: List<&2, Ask>, a: Acct) -> Grant:
  match a:
    case Acct{free, spent, lent, over, holds, until}:
      reserve.open(allows(phase, use), use, phase, id, now, base, keep, want, less, free, spent, lent, over, holds, until)

# Settle
# ------

# avail (what is free plus what was held) pays act
def settle.take(+avail: Amt, +act: Amt, spent: Amt, lent: Amt, over: Amt, rest: List<&2, Hold>, until: Nat) -> Acct:
  Acct{sub4(avail, act), add4(spent, act), lent, add4(over, sub4(act, avail)), rest, until}

def settle.if(h: Bool, +id: Nat, +act: Amt, free: Amt, spent: Amt, lent: Amt, over: Amt, +holds: List<&2, Hold>, until: Nat) -> Acct:
  match h:
    case True{}:
      settle.take(add4(free, owed(id, holds)), act, spent, lent, over, others(id, holds), until)
    case False{}:
      Acct{free, spent, lent, over, holds, until}

# the actual spend act replaces what is held under id: the rest of the
# hold is free again; a spend past the hold is taken from free, and past
# that it is an overrun. An id that is not held changes nothing.
def settle(+id: Nat, +act: Amt, a: Acct) -> Acct:
  match a:
    case Acct{free, spent, lent, over, +holds, until}:
      settle.if(held(id, holds), id, act, free, spent, lent, over, holds, until)

# Children
# --------

def carve.fit(l: Maybe<&2, Dim>, +now: Nat, +want: Ask, free: Amt, spent: Amt, lent: Amt, over: Amt, holds: List<&2, Hold>, until: Nat) -> Carve:
  match l:
    case None{}:
      match want:
        case Ask{+x, m}:
          Carved{Acct{sub4(free, x), spent, add4(lent, x), over, holds, until}, Acct{x, zero(), zero(), zero(), Nil{}, Nat.add(now, m)}}
    case Some{d}:
      Kept{Short{d}}

# a child's own budget want, asked by an agent in phase `phase` at time
# `now`: its amount leaves the parent's free (which keeps base, the
# reserves of the agents above the child) and is lent; the child's
# deadline is want's duration from now, which must end base before the
# parent's. Only a Working agent carves.
def carve(phase: Phase, +now: Nat, +want: Ask, base: Ask, a: Acct) -> Carve:
  match phase:
    case Working{}:
      match a:
        case Acct{+free, spent, lent, over, holds, +until}:
          carve.fit(lack(need(Final{}, base, Ask{zero(), 0n}, want), free, now, until), now, want, free, spent, lent, over, holds, until)
    case WrapUp{}:
      Kept{Stopped{}}
    case Exhausted{}:
      Kept{Stopped{}}

def close.idle(idle: Bool, +cf: Amt, +cs: Amt, +co: Amt, pf: Amt, ps: Amt, pl: Amt, po: Amt, ph: List<&2, Hold>, pu: Nat) -> Close:
  match idle:
    case True{}:
      +avail = add4(pf, cf)
      Closed{Acct{sub4(avail, co), add4(ps, cs), sub4(pl, sub4(add4(cf, cs), co)), add4(po, sub4(co, avail)), ph, pu}, Acct{zero(), zero(), zero(), zero(), Nil{}, 0n}}
    case False{}:
      Busy{}

def close.holds(hs: List<&2, Hold>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# an idle child (no hold, nothing lent) hands back what is free; its
# spend becomes the parent's; its overrun is taken from the parent's free
# and, past that, is the parent's overrun. The child is left empty, its
# deadline passed.
def close(child: Acct, parent: Acct) -> Close:
  match child parent:
    case Acct{cf, cs, cl, co, ch, cu} Acct{pf, ps, pl, po, ph, pu}:
      close.idle(Bool.and(close.holds(ch), is_zero4(cl)), cf, cs, co, pf, ps, pl, po, ph, pu)

# Funding
# -------

# n more budget and n's duration more time: the amount repays the
# overrun first
def fund(+n: Ask, a: Acct) -> Acct:
  match n a:
    case Ask{+x, m} Acct{free, spent, lent, +over, holds, until}:
      Acct{add4(free, sub4(x, over)), spent, lent, sub4(over, x), holds, Nat.add(until, m)}

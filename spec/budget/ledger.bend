# budget (spec): what the laws of area budget (laws/budget.bend) speak of,
# over the types of bend/budget.bend: what an account measures in one
# dimension, when an ask fits, which offer is taken, what each phase
# admits. A spec: the shipped code never calls it.
#
# S1: a budget has four spent dimensions (money, tokens, tool calls,
#     model requests) and a deadline (wall-clock time); every rule holds
#     in each spent dimension by itself, and an amount is taken in all
#     four or in none.
# S2: the budget of an account in a spent dimension is what is free, plus
#     what is held by open reservations, plus what is spent, plus what is
#     lent to children given their own budget (`net`). Only funding
#     changes it; a spend past the funding is the overrun, counted apart.
# S3: an ask fits when, in every spent dimension, its amount, the
#     reserves of the agents above (`base`) and, for work and a side
#     request, the asking agent's own final-answer reserve (`keep`) are
#     within what is free, and when, started now, its duration and those
#     reserves' durations end by the deadline.
# S4: of the offers, in order, the first that fits is taken; none taken
#     means none fits.
# S5: a Working agent is admitted work, side requests and a final
#     answer; a WrapUp agent a final answer and side requests; an
#     Exhausted agent nothing. Work that finds no offer fitting moves the
#     agent to WrapUp; a final answer that finds none moves it to
#     Exhausted; a side request (a request of the agent that is not its
#     own turn: a title, a classifier, a compaction, a memory or side
#     question) that finds none leaves its phase as it was.
# S6: a child is idle when it has no open reservation and has lent
#     nothing: only then can it be closed. `lent` counts amounts, so a
#     child whose only live child was carved with nothing has lent
#     nothing; that a child is never closed before its live children is
#     the ledger's order (crates/eukhe-budget reclaim closes them first),
#     not this model's: an account here does not know its children.

import Base
import ../../bend/budget.bend as B

# Measures
# --------

# the amount x in spent dimension d (S1); time is no spent dimension:
# its amount is zero
def at(d: B.Dim, x: B.Amt) -> Nat:
  match d:
    case B.Cost{}:
      match x:
        case B.Amt{c, k, n, r}:
          c
    case B.Tok{}:
      match x:
        case B.Amt{c, k, n, r}:
          k
    case B.Time{}:
      0n
    case B.Calls{}:
      match x:
        case B.Amt{c, k, n, r}:
          n
    case B.Reqs{}:
      match x:
        case B.Amt{c, k, n, r}:
          r

def amt(x: B.Ask) -> B.Amt:
  match x:
    case B.Ask{a, m}:
      a

def ms(x: B.Ask) -> Nat:
  match x:
    case B.Ask{a, m}:
      m

def free(a: B.Acct) -> B.Amt:
  match a:
    case B.Acct{f, s, l, o, h, u}:
      f

def spent(a: B.Acct) -> B.Amt:
  match a:
    case B.Acct{f, s, l, o, h, u}:
      s

def lent(a: B.Acct) -> B.Amt:
  match a:
    case B.Acct{f, s, l, o, h, u}:
      l

def over(a: B.Acct) -> B.Amt:
  match a:
    case B.Acct{f, s, l, o, h, u}:
      o

def holds(a: B.Acct) -> List<&2, B.Hold>:
  match a:
    case B.Acct{f, s, l, o, h, u}:
      h

def until(a: B.Acct) -> Nat:
  match a:
    case B.Acct{f, s, l, o, h, u}:
      u

# what the open reservations hold in dimension d (S2)
def held(+d: B.Dim, hs: List<&2, B.Hold>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case Con{h, t}:
      match h:
        case B.Hold{i, x}:
          Nat.add(at(d, x), held(d, t))

def held_of.one(same: Bool, x: Nat, rest: Nat) -> Nat:
  match same:
    case True{}:
      Nat.add(x, rest)
    case False{}:
      rest

# what the reservations under id hold in dimension d
def held_of(+id: Nat, +d: B.Dim, hs: List<&2, B.Hold>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case Con{h, t}:
      match h:
        case B.Hold{i, x}:
          held_of.one(Nat.is_eq(i, id), at(d, x), held_of(id, d, t))

# a reservation under id is open
def has(+id: Nat, hs: List<&2, B.Hold>) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case Con{h, t}:
      match h:
        case B.Hold{i, x}:
          Bool.or(Nat.is_eq(i, id), has(id, t))

# the budget of the account in dimension d: free, held, spent and lent
# (S2)
def net(+d: B.Dim, a: B.Acct) -> Nat:
  match a:
    case B.Acct{f, s, l, o, h, u}:
      Nat.add(at(d, f), Nat.add(held(d, h), Nat.add(at(d, s), at(d, l))))

# Fitting
# -------

# nothing: no amount, no time
def nothing() -> B.Ask:
  B.Ask{B.Amt{0n, 0n, 0n, 0n}, 0n}

# what an ask leaves for the asking agent's own final answer: work and a
# side request its reserve, a final answer nothing (S3)
def keep_of(u: B.Use, keep: B.Ask) -> B.Ask:
  match u:
    case B.Work{}:
      keep
    case B.Final{}:
      nothing()
    case B.Side{}:
      keep

# the ask c fits what is free in spent dimension d, with the reserves
# (S3)
def fits_in(u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +d: B.Dim) -> Bool:
  Nat.is_le(Nat.add(at(d, amt(c)), Nat.add(at(d, amt(base)), at(d, amt(keep_of(u, keep))))), at(d, f))

# the ask c, started at now, ends by the deadline with the reserves'
# durations (S3)
def on_time(u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +now: Nat, +until: Nat) -> Bool:
  Nat.is_le(Nat.add(now, Nat.add(ms(c), Nat.add(ms(base), ms(keep_of(u, keep))))), until)

# the ask c fits what is free in every spent dimension and ends on time
# (S1, S3)
def fits(+u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +until: Nat) -> Bool:
  Bool.and(fits_in(u, base, keep, c, f, B.Cost{}), Bool.and(fits_in(u, base, keep, c, f, B.Tok{}), Bool.and(on_time(u, base, keep, c, now, until), Bool.and(fits_in(u, base, keep, c, f, B.Calls{}), fits_in(u, base, keep, c, f, B.Reqs{})))))

# the ask c fails in dimension d: an amount past free, or (time) past the
# deadline (S3)
def short_in(u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +until: Nat, d: B.Dim) -> Bool:
  match d:
    case B.Time{}:
      Bool.not(on_time(u, base, keep, c, now, until))
    case B.Cost{}:
      Bool.not(fits_in(u, base, keep, c, f, B.Cost{}))
    case B.Tok{}:
      Bool.not(fits_in(u, base, keep, c, f, B.Tok{}))
    case B.Calls{}:
      Bool.not(fits_in(u, base, keep, c, f, B.Calls{}))
    case B.Reqs{}:
      Bool.not(fits_in(u, base, keep, c, f, B.Reqs{}))

# no offer of xs fits (S4)
def none_fit(+u: B.Use, +base: B.Ask, +keep: B.Ask, xs: List<&2, B.Ask>, +f: B.Amt, +now: Nat, +until: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(Bool.not(fits(u, base, keep, x, f, now, until)), none_fit(u, base, keep, t, f, now, until))

# the offer at place i
def nth(i: Nat, xs: List<&2, B.Ask>) -> Maybe<&2, B.Ask>:
  match i:
    case 0n:
      match xs:
        case Nil{}:
          None{}
        case Con{x, t}:
          Some{x}
    case 1n+j:
      match xs:
        case Nil{}:
          None{}
        case Con{x, t}:
          nth(j, t)

# the offers before place i
def before(i: Nat, xs: List<&2, B.Ask>) -> List<&2, B.Ask>:
  match i:
    case 0n:
      Nil{}
    case 1n+j:
      match xs:
        case Nil{}:
          Nil{}
        case Con{x, t}:
          x <> before(j, t)

# the last of the offers x and then xs
def last(xs: List<&2, B.Ask>, x: B.Ask) -> B.Ask:
  match xs:
    case Nil{}:
      x
    case Con{y, t}:
      last(t, y)

# a is within b in every spent dimension and in duration
def le(+a: B.Ask, +b: B.Ask) -> Bool:
  Bool.and(Nat.is_le(at(B.Cost{}, amt(a)), at(B.Cost{}, amt(b))), Bool.and(Nat.is_le(at(B.Tok{}, amt(a)), at(B.Tok{}, amt(b))), Bool.and(Nat.is_le(at(B.Calls{}, amt(a)), at(B.Calls{}, amt(b))), Bool.and(Nat.is_le(at(B.Reqs{}, amt(a)), at(B.Reqs{}, amt(b))), Nat.is_le(ms(a), ms(b))))))

# a and b together, in every spent dimension and in duration
def plus(+a: B.Ask, +b: B.Ask) -> B.Ask:
  B.Ask{B.Amt{Nat.add(at(B.Cost{}, amt(a)), at(B.Cost{}, amt(b))), Nat.add(at(B.Tok{}, amt(a)), at(B.Tok{}, amt(b))), Nat.add(at(B.Calls{}, amt(a)), at(B.Calls{}, amt(b))), Nat.add(at(B.Reqs{}, amt(a)), at(B.Reqs{}, amt(b)))}, Nat.add(ms(a), ms(b))}

# Phases
# ------

# what a phase admits (S5): Working work, a final answer and side
# requests, WrapUp a final answer and side requests, Exhausted nothing
def allows(p: B.Phase, u: B.Use) -> Bool:
  match p u:
    case B.Working{} B.Work{}:
      True{}
    case B.Working{} B.Final{}:
      True{}
    case B.Working{} B.Side{}:
      True{}
    case B.WrapUp{} B.Work{}:
      False{}
    case B.WrapUp{} B.Final{}:
      True{}
    case B.WrapUp{} B.Side{}:
      True{}
    case B.Exhausted{} B.Work{}:
      False{}
    case B.Exhausted{} B.Final{}:
      False{}
    case B.Exhausted{} B.Side{}:
      False{}

# the phase after no offer fit, of an agent in phase p (S5): work WrapUp,
# a final answer Exhausted, a side request p
def after(u: B.Use, p: B.Phase) -> B.Phase:
  match u:
    case B.Work{}:
      B.WrapUp{}
    case B.Final{}:
      B.Exhausted{}
    case B.Side{}:
      p

def working(p: B.Phase) -> Bool:
  match p:
    case B.Working{}:
      True{}
    case B.WrapUp{}:
      False{}
    case B.Exhausted{}:
      False{}

# Answers
# -------

def granted(g: B.Grant) -> Bool:
  match g:
    case B.Granted{i, c, a, t}:
      True{}
    case B.Refused{w, p}:
      False{}

def carved(c: B.Carve) -> Bool:
  match c:
    case B.Carved{p, k}:
      True{}
    case B.Kept{w}:
      False{}

def closed(c: B.Close) -> Bool:
  match c:
    case B.Closed{p, k}:
      True{}
    case B.Busy{}:
      False{}

# the phase a refusal for a short dimension moves the agent to; none for
# a grant or another refusal
def short_to(g: B.Grant) -> Maybe<&2, B.Phase>:
  match g:
    case B.Granted{i, c, a, t}:
      None{}
    case B.Refused{w, p}:
      match w:
        case B.Short{d}:
          Some{p}
        case B.Held{}:
          None{}
        case B.Stopped{}:
          None{}

# a carve kept for a short dimension
def kept_short(c: B.Carve) -> Bool:
  match c:
    case B.Carved{p, k}:
      False{}
    case B.Kept{w}:
      match w:
        case B.Short{d}:
          True{}
        case B.Held{}:
          False{}
        case B.Stopped{}:
          False{}

def no_holds(hs: List<&2, B.Hold>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# a is zero in every spent dimension
def none4(+a: B.Amt) -> Bool:
  Bool.and(Nat.is_eq(at(B.Cost{}, a), 0n), Bool.and(Nat.is_eq(at(B.Tok{}, a), 0n), Bool.and(Nat.is_eq(at(B.Calls{}, a), 0n), Nat.is_eq(at(B.Reqs{}, a), 0n))))

# the child has no open reservation and has lent nothing (S6)
def idle(+c: B.Acct) -> Bool:
  Bool.and(no_holds(holds(c)), none4(lent(c)))

# an account that holds nothing, whose deadline has passed: a closed
# child
def empty() -> B.Acct:
  B.Acct{B.Amt{0n, 0n, 0n, 0n}, B.Amt{0n, 0n, 0n, 0n}, B.Amt{0n, 0n, 0n, 0n}, B.Amt{0n, 0n, 0n, 0n}, Nil{}, 0n}

# eukhe: the proof of LAW budget_share_leaves_others
#
# PROOF: some offer is within the share, so the start's is
# (budget_share_first_within's lemma bsm.fw): in money and in tokens, at
# most what is free past the reserves R divided by n = m + 1 (Nat.max(n, 1)
# is n: bsm.max_succ). Then n times it is at most R (bsa.mul_div_le) and
# what it leaves past R, n times, is at least m times R (bsa.leaves).

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../spec/budget/ledger.bend as S
import ../../laws/budget_share.bend as BudgetShare
import ./base/model.bend as BSM
import ./base/arith.bend as BSA
import ../budget/base/reserve.bend as BR

# in dimension d
def bslo.d(+m: Nat, +d: B.Dim, +base: B.Ask, +keep: B.Ask, +free: B.Amt, +c: B.Ask, w: {BudgetShare.ss_share_in(1n+m, d, base, keep, free, c) == True{} : Bool}) -> {Nat.is_le(Nat.mul(m, BudgetShare.ss_room(d, base, keep, free)), Nat.mul(1n+m, Nat.sub(BudgetShare.ss_room(d, base, keep, free), S.at(d, S.amt(c))))) == True{} : Bool}:
  +r = BudgetShare.ss_room(d, base, keep, free)
  +x = S.at(d, S.amt(c))
  BSA.bsa.leaves(m, r, x, Equal.trans(Bool, Nat.is_le(x, Nat.div(r, 1n+m)), Nat.is_le(x, Nat.div(r, Nat.max(1n+m, 1n))), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(x, Nat.div(r, z)), 1n+m, Nat.max(1n+m, 1n), Equal.sym(Nat, Nat.max(1n+m, 1n), 1n+m, BSM.bsm.max_succ(m))), w))

# for a shared use within the share
def bslo.use(u: B.Use, +m: Nat, +base: B.Ask, +keep: B.Ask, +free: B.Amt, +c: B.Ask, shared: {BudgetShare.ss_shared(u) == True{} : Bool}, wc: {BudgetShare.ss_within(1n+m, u, base, keep, free, c) == True{} : Bool}) -> {Nat.is_le(Nat.mul(m, BudgetShare.ss_room(B.Cost{}, base, keep, free)), Nat.mul(1n+m, Nat.sub(BudgetShare.ss_room(B.Cost{}, base, keep, free), S.at(B.Cost{}, S.amt(c))))) == True{} : Bool} & {Nat.is_le(Nat.mul(m, BudgetShare.ss_room(B.Tok{}, base, keep, free)), Nat.mul(1n+m, Nat.sub(BudgetShare.ss_room(B.Tok{}, base, keep, free), S.at(B.Tok{}, S.amt(c))))) == True{} : Bool}:
  match u:
    case B.Work{}:
      +w0 = wc
      (bslo.d(m, B.Cost{}, base, keep, free, c, BR.br.and_l(BudgetShare.ss_share_in(1n+m, B.Cost{}, base, keep, free, c), BudgetShare.ss_share_in(1n+m, B.Tok{}, base, keep, free, c), w0)), bslo.d(m, B.Tok{}, base, keep, free, c, BR.br.and_r(BudgetShare.ss_share_in(1n+m, B.Cost{}, base, keep, free, c), BudgetShare.ss_share_in(1n+m, B.Tok{}, base, keep, free, c), w0)))
    case B.Final{}:
      BR.br.absurd({Nat.is_le(Nat.mul(m, BudgetShare.ss_room(B.Cost{}, base, keep, free)), Nat.mul(1n+m, Nat.sub(BudgetShare.ss_room(B.Cost{}, base, keep, free), S.at(B.Cost{}, S.amt(c))))) == True{} : Bool} & {Nat.is_le(Nat.mul(m, BudgetShare.ss_room(B.Tok{}, base, keep, free)), Nat.mul(1n+m, Nat.sub(BudgetShare.ss_room(B.Tok{}, base, keep, free), S.at(B.Tok{}, S.amt(c))))) == True{} : Bool}, shared)
    case B.Side{}:
      +w0 = wc
      (bslo.d(m, B.Cost{}, base, keep, free, c, BR.br.and_l(BudgetShare.ss_share_in(1n+m, B.Cost{}, base, keep, free, c), BudgetShare.ss_share_in(1n+m, B.Tok{}, base, keep, free, c), w0)), bslo.d(m, B.Tok{}, base, keep, free, c, BR.br.and_r(BudgetShare.ss_share_in(1n+m, B.Cost{}, base, keep, free, c), BudgetShare.ss_share_in(1n+m, B.Tok{}, base, keep, free, c), w0)))

# the start's offer c is within the share
def bslo.top(+m: Nat, +use: B.Use, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +free: B.Amt, +now: Nat, +until: Nat, +c: B.Ask, shared: {BudgetShare.ss_shared(use) == True{} : Bool}, at: {S.nth(Bs.start(1n+m, use, base, keep, want, less, free, now, until), want <> less) == Some{c} : Maybe<&2, B.Ask>}, fw: {BudgetShare.ss_mok(1n+m, use, base, keep, S.nth(Bs.start(1n+m, use, base, keep, want, less, free, now, until), want <> less), free, now, until) == True{} : Bool} & {BudgetShare.ss_none_ok(1n+m, use, base, keep, S.before(Bs.start(1n+m, use, base, keep, want, less, free, now, until), want <> less), free, now, until) == True{} : Bool}) -> {Nat.is_le(Nat.mul(m, BudgetShare.ss_room(B.Cost{}, base, keep, free)), Nat.mul(1n+m, Nat.sub(BudgetShare.ss_room(B.Cost{}, base, keep, free), S.at(B.Cost{}, S.amt(c))))) == True{} : Bool} & {Nat.is_le(Nat.mul(m, BudgetShare.ss_room(B.Tok{}, base, keep, free)), Nat.mul(1n+m, Nat.sub(BudgetShare.ss_room(B.Tok{}, base, keep, free), S.at(B.Tok{}, S.amt(c))))) == True{} : Bool}:
  (fa, fb) = fw
  +oc = Equal.trans(Bool, BudgetShare.ss_ok(1n+m, use, base, keep, c, free, now, until), BudgetShare.ss_mok(1n+m, use, base, keep, S.nth(Bs.start(1n+m, use, base, keep, want, less, free, now, until), want <> less), free, now, until), True{}, Equal.cong(Maybe<&2, B.Ask>, Bool, z => BudgetShare.ss_mok(1n+m, use, base, keep, z, free, now, until), Some{c}, S.nth(Bs.start(1n+m, use, base, keep, want, less, free, now, until), want <> less), Equal.sym(Maybe<&2, B.Ask>, S.nth(Bs.start(1n+m, use, base, keep, want, less, free, now, until), want <> less), Some{c}, at)), fa)
  bslo.use(use, m, base, keep, free, c, shared, BR.br.and_r(S.fits(use, base, keep, c, free, now, until), BudgetShare.ss_within(1n+m, use, base, keep, free, c), oc))

def BudgetShare.budget_share_leaves_others(m, use, base, keep, want, less, free, now, until, c, shared, some, at):
  bslo.top(m, use, base, keep, want, less, free, now, until, c, shared, at, BSM.bsm.fw(Bs.first(want <> less, 1n+m, use, base, keep, free, now, until), Bs.last(want <> less, use, base, keep, free, now, until), 1n+m, use, base, keep, free, now, until, want <> less, BSM.bsm.first_ok(want <> less, 1n+m, use, base, keep, free, now, until), some))

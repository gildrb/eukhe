# eukhe: the proof of LAW budget_share_never_exceeds
#
# PROOF: the reservation from the start's offer on is a reservation: what
# every grant says (budget_grant_within, budget_grant_on_time: br.within,
# br.in_time from br.res_is) holds of it.

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../spec/budget/ledger.bend as S
import ../../laws/budget_share.bend as BudgetShare
import ./base/model.bend as BSM
import ../budget/base/reserve.bend as BR

def bsne.join(+u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +i: Nat, +c: B.Ask, +a2: B.Acct, +lo: Bool, +d: B.Dim, w: {Nat.add(S.at(d, S.free(a2)), S.at(d, S.amt(c))) == S.at(d, S.free(a)) : Nat} & {S.fits_in(u, base, keep, c, S.free(a), d) == True{} : Bool}, t: {S.on_time(u, base, keep, c, now, S.until(a)) == True{} : Bool} & {S.until(a2) == S.until(a) : Nat}) -> {Nat.add(S.at(d, S.free(a2)), S.at(d, S.amt(c))) == S.at(d, S.free(a)) : Nat} & ({S.fits_in(u, base, keep, c, S.free(a), d) == True{} : Bool} & {S.on_time(u, base, keep, c, now, S.until(a)) == True{} : Bool}):
  (w0, w1) = w
  (t0, t1) = t
  (w0, (w1, t0))

def BudgetShare.budget_share_never_exceeds(n, use, p, id, now, base, keep, step, want, less, a, i, c, a2, lo, d, g):
  +w2 = BudgetShare.ss_offer(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want, less)
  +l2 = BudgetShare.ss_after(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want <> less)
  +g0 = g
  bsne.join(use, p, id, now, base, keep, step, w2, l2, a, i, c, a2, lo, d, BR.br.within(use, p, id, now, base, keep, step, w2, l2, a, i, c, a2, lo, d, BR.br.res_is(use, p, id, now, base, keep, step, w2, l2, a, B.Granted{i, c, a2, lo}, g0)), BR.br.in_time(use, p, id, now, base, keep, step, w2, l2, a, i, c, a2, lo, BR.br.res_is(use, p, id, now, base, keep, step, w2, l2, a, B.Granted{i, c, a2, lo}, g0)))

# eukhe: the proof of LAW budget_share_refuses_alike
#
# PROOF: when no offer fits, the start is 0 (bsm.nf0): both reservations
# are the same, and neither grants (bsr.holds_none). When one fits, the
# start's offer fits (bsm.start_fits): from it the phase and the id decide
# alike (refused as stopped, as held, else granted on both sides:
# bsr.alike2), and a grant is of it, at place 0, as it fits (bsr.holds_c0).

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../spec/budget/ledger.bend as S
import ../../laws/budget_share.bend as BudgetShare
import ./base/model.bend as BSM
import ./base/reserve.bend as BSR

def bsra.top(b: Bool, +n: Nat, +use: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, eb: {S.none_fit(use, base, keep, want <> less, S.free(a), now, S.until(a)) == b : Bool}) -> BSR.bsr.Alike(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), use, p, id, now, base, keep, step, want, less, a):
  match b:
    case True{}:
      +e0 = eb
      +z = BSM.bsm.nf0(Bs.first(want <> less, n, use, base, keep, S.free(a), now, S.until(a)), Bs.last(want <> less, use, base, keep, S.free(a), now, S.until(a)), n, use, base, keep, S.free(a), now, S.until(a), want <> less, BSM.bsm.first_ok(want <> less, n, use, base, keep, S.free(a), now, S.until(a)), BSM.bsm.last_ok(want <> less, use, base, keep, S.free(a), now, S.until(a)), e0)
      %Equal.sym(Nat, Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), 0n, z) : BSR.bsr.Alike(_, use, p, id, now, base, keep, step, want, less, a)
      ({==}, BSR.bsr.holds_none(B.reserve(use, p, id, now, base, keep, step, want, less, a), use, p, id, now, base, keep, step, want, less, a, Some{want}, {==}, e0))
    case False{}:
      +e0 = eb
      BSR.bsr.alike_m(S.nth(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want <> less), Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), use, p, id, now, base, keep, step, want, less, a, {==}, BSM.bsm.start_fits(Bs.first(want <> less, n, use, base, keep, S.free(a), now, S.until(a)), Bs.last(want <> less, use, base, keep, S.free(a), now, S.until(a)), n, use, base, keep, S.free(a), now, S.until(a), want <> less, BSM.bsm.first_ok(want <> less, n, use, base, keep, S.free(a), now, S.until(a)), BSM.bsm.last_ok(want <> less, use, base, keep, S.free(a), now, S.until(a)), e0), e0)

def BudgetShare.budget_share_refuses_alike(n, use, p, id, now, base, keep, step, want, less, a):
  bsra.top(S.none_fit(use, base, keep, want <> less, S.free(a), now, S.until(a)), n, use, p, id, now, base, keep, step, want, less, a, {==})

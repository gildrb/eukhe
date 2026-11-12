# eukhe: the proof of LAW budget_side_final_reserve_kept
#
# PROOF: a side request fits as work does (the same need: the ask, base
# and keep), so a granted side request fits with the reserves, amount and
# time; the rest is budget_final_reserve_kept's proof (br.final_kept).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_side_final_reserve_kept(p, id, now, base, keep, step, want, less, a, i, c, a2, lo, f, p2, id2, now2, k2, s2, g, within, ok, fresh, soon):
  BR.br.final_kept(B.Side{}, p, id, now, base, keep, step, want, less, a, i, c, a2, lo, f, p2, id2, now2, k2, s2, {==}, BR.br.res_is(B.Side{}, p, id, now, base, keep, step, want, less, a, B.Granted{i, c, a2, lo}, g), within, ok, fresh, soon)

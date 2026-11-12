# eukhe: the proof of LAW budget_base_kept
#
# PROOF: any grant fits with the reserves above in every dimension; what it
# left free is free less the amount, so a final answer within those
# reserves fits it with no reserve (br.base_fits); the deadline stays,
# so on time by it is on time; then it is granted as in
# budget_grant_when_fits.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_base_kept(use, p, id, now, base, keep, want, less, a, i, c, a2, t, f, p2, id2, now2, k2, g, within, ok, fresh, ontime):
  BR.br.base_kept(use, p, id, now, base, keep, want, less, a, i, c, a2, t, f, p2, id2, now2, k2, BR.br.res_is(use, p, id, now, base, keep, want, less, a, B.Granted{i, c, a2, t}, g), within, ok, fresh, ontime)

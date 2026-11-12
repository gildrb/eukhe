# eukhe: the proof of LAW budget_final_reserve_kept
#
# PROOF: granted work fits with the reserves, amount and time; what it left
# free is free less the amount, so a final answer within the reserve
# fits it in each dimension, and, asked by the time the work ends, it
# ends by the deadline (br.final_fits); then it is granted as in
# budget_grant_when_fits.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_final_reserve_kept(p, id, now, base, keep, want, less, a, i, c, a2, t, f, p2, id2, now2, k2, g, within, ok, fresh, soon):
  BR.br.final_kept(id, now, base, keep, want, less, a, i, c, a2, t, f, p2, id2, now2, k2, BR.br.res_is(B.Work{}, p, id, now, base, keep, want, less, a, B.Granted{i, c, a2, t}, g), within, ok, fresh, soon)

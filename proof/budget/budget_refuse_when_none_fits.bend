# eukhe: the proof of LAW budget_refuse_when_none_fits
#
# PROOF: admitted under a fresh id, the reservation picks among the offers
# (br.pick_ok); a fit pick is an offer that fits, which none does
# (br.nf_nth), so the pick finds none and the refusal is short, in the
# phase after no fit.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_refuse_when_none_fits(use, p, id, now, base, keep, want, less, a, ok, fresh, none):
  BR.br.none_short(a, use, p, id, now, base, keep, want, less, ok, fresh, none)

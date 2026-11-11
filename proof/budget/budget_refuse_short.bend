# eukhe: the proof of LAW budget_refuse_short
#
# PROOF: a refusal for a short dimension comes only from a pick that found
# no offer fitting (br.res_is): none fits, the last is short in that
# dimension, and the phase is the one after no fit.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_refuse_short(use, p, id, now, base, keep, want, less, a, d, p2, g):
  BR.br.res_is(use, p, id, now, base, keep, want, less, a, B.Refused{B.Short{d}, p2}, g)

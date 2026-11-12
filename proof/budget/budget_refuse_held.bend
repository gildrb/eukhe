# eukhe: the proof of LAW budget_refuse_held
#
# PROOF: admitted, the code's held is the spec's has (br.held_is): the id
# held, the reservation is refused as held in the same phase.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_refuse_held(use, p, id, now, base, keep, step, want, less, a, ok, dup):
  BR.br.dup(a, use, p, id, now, base, keep, step, want, less, ok, dup)

# eukhe: the proof of LAW budget_refuse_stopped
#
# PROOF: the code's admission is the spec's (br.allows_is): not admitted,
# the reservation is refused as stopped in the same phase.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_refuse_stopped(use, p, id, now, base, keep, step, want, less, a, no):
  BR.br.stopped(a, use, p, id, now, base, keep, step, want, less, no)

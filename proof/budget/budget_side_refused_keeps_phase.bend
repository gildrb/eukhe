# eukhe: the proof of LAW budget_side_refused_keeps_phase
#
# PROOF: every way a side request is refused (the phase does not admit
# it, its id is held, no offer fits) answers the asking agent's phase:
# the first two pass it through, and the phase after no fit of a side
# request is the phase it was asked in (br.side_keeps).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_side_refused_keeps_phase(p, id, now, base, keep, step, want, less, a, w, p2, g):
  %g : BR.br.KeepsPhase(_, p)
  BR.br.side_keeps(p, id, now, base, keep, step, want, less, a)

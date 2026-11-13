# eukhe: the proof of LAW budget_grant_when_fits
#
# PROOF: the phase admits the request and the id is not held, so the
# reservation picks among the offers; the pick is the first that fits or
# none fits (br.pick_ok), and one fits, so it is granted.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_grant_when_fits(use, p, id, now, base, keep, step, want, less, a, ok, fresh, some):
  BR.br.when_fits(a, use, p, id, now, base, keep, step, want, less, ok, fresh, some)

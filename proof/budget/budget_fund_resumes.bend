# eukhe: the proof of LAW budget_fund_resumes
#
# PROOF: the funded account keeps the holds, so the id is still not held;
# free is at least the ask and the reserves in every dimension (the
# funding past the overrun is exactly that) and the deadline is at least
# now and their durations (br.le_top), so the one offer fits and, the
# agent Working, it is granted (br.resumes).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR

def Budget.budget_fund_resumes(id, now, base, keep, step, c, a, fresh):
  BR.br.resumes(c, base, keep, step, a, id, now, fresh)

# eukhe: the proof of LAW budget_settle_keeps_others
#
# PROOF: an id not held: nothing changes. A held id: the holds left are the
# holds of every other id, in order; a hold dropped is under the settled id,
# which is not j, so what j holds is unchanged (induction on the holds).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ./base/settle.bend as BS

def Budget.budget_settle_keeps_others(id, act, a, j, d, other):
  match a:
    case B.Acct{f, s, l, o, hs, u}:
      BS.bs.keeps_if(B.held(id, hs), j, id, act, f, s, l, o, hs, u, d, other)

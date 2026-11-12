# eukhe: the proof of LAW budget_settle_once
#
# PROOF: after a settlement the id is not held: a found id leaves only the
# holds of the other ids, an id not found was not held. So the second
# settlement finds nothing and changes nothing.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ./base/settle.bend as BS

def Budget.budget_settle_once(id, act, again, a):
  BS.bs.inert(id, again, B.settle(id, act, a), BS.bs.settled(id, act, a))

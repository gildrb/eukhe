# eukhe: the proof of LAW context_plan_exact

import Base
import ../../bend/context_order.bend as Co
import ../../laws/context_order.bend as ContextOrder
import ./base.bend as LACo

# PROOF of LAW context_plan_exact: the split is the spec's (co.split: the last assistant found walking forward is the one found from the end), the prefix is the spec's (co.take), and both orders are the spec's (co.order).

def ContextOrder.context_plan_exact(ms):
  LACo.co.plan(ms)

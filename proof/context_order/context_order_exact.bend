# eukhe: the proof of LAW context_order_exact

import Base
import ../../bend/context_order.bend as Co
import ../../laws/context_order.bend as ContextOrder
import ./base.bend as LACo

# PROOF of LAW context_order_exact: the code orders by the window of each assistant, the spec by a scan per call: they agree (co.order).

def ContextOrder.context_order_exact(ms):
  LACo.co.order(ms, 0n)

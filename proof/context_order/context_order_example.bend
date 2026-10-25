# eukhe: the proof of LAW context_order_example

import Base
import ../../bend/context_order.bend as Co
import ../../laws/context_order.bend as ContextOrder
import ./base.bend as LACo

# PROOF of LAW context_order_example: each anchor computes.

def ContextOrder.context_order_example():
  ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))

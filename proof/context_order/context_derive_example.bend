# eukhe: the proof of LAW context_derive_example

import Base
import ../../bend/context_order.bend as Co
import ../../laws/context_order.bend as ContextOrder
import ./base.bend as LACo

# PROOF of LAW context_derive_example: each anchor computes.

def ContextOrder.context_derive_example():
  ({==}, ({==}, {==}))

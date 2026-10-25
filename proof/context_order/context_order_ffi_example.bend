# eukhe: the proof of LAW context_order_ffi_example

import Base
import ../../bend/context_order.bend as Co
import ../../bend/ffi_context_order.bend as FCo
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/context_order.bend as ContextOrder
import ./base.bend as LACo
import ./base/read.bend as LACoRead
import ./base/reply.bend as LACoReply

# PROOF of LAW context_order_ffi_example: the anchor computes.

def ContextOrder.context_order_ffi_example():
  {==}

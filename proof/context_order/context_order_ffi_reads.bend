# eukhe: the proof of LAW context_order_ffi_reads

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

# PROOF of LAW context_order_ffi_reads: each decoder reads its spelled value back, the rest untouched (cot.req).

def ContextOrder.context_order_ffi_reads(q, rest, h):
  LACoRead.cot.req(q, rest, h)

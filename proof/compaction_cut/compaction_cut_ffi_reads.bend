# eukhe: the proof of LAW compaction_cut_ffi_reads

import Base
import ../../bend/context_order.bend as Co
import ../../bend/compaction_cut.bend as Cc
import ../../bend/ffi_compaction_cut.bend as FCc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/context_order.bend as ContextOrder
import ../../laws/compaction_cut.bend as CompactionCut
import ../context_order/base.bend as LACo
import ./base/read.bend as LACcRead

# PROOF of LAW compaction_cut_ffi_reads: each decoder reads its spelled value back, the rest untouched (cct.req).

def CompactionCut.compaction_cut_ffi_reads(q, rest, h):
  LACcRead.cct.req(q, rest, h)

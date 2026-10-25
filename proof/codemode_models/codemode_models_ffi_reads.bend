# eukhe: the proof of LAW codemode_models_ffi_reads

import Base
import ../../bend/codemode_models.bend as Mod
import ../../bend/ffi_codemode_models.bend as FMod
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/codemode_models/entry.bend as CodemodeModelsEntry
import ../context_order/base.bend as LACo
import ./base/read.bend as LACmRead

# PROOF of LAW codemode_models_ffi_reads: each decoder reads its spelled value back, the rest untouched (cmq.req).

def CodemodeModelsEntry.codemode_models_ffi_reads(q, rest, h):
  LACmRead.cmq.req(q, rest, h)

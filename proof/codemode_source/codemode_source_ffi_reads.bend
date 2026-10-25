# eukhe: the proof of LAW codemode_source_ffi_reads

import Base
import ../../bend/codemode_source.bend as Src
import ../../bend/ffi_codemode_source.bend as FSrc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/codemode_source.bend as CodemodeSource
import ./base/read.bend as LACsRead

# PROOF of LAW codemode_source_ffi_reads: each decoder reads its spelled value back, the rest untouched (csq.req).

def CodemodeSource.codemode_source_ffi_reads(f, rest, h):
  LACsRead.csq.req(f, rest, h)

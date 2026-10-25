# eukhe: the proof of LAW codemode_source_ffi_example

import Base
import ../../bend/codemode_source.bend as Src
import ../../bend/ffi_codemode_source.bend as FSrc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/codemode_source.bend as CodemodeSource
import ../context_order/base.bend as LACo

# PROOF of LAW codemode_source_ffi_example: the anchor computes.

def CodemodeSource.codemode_source_ffi_example():
  {==}

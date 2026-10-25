# eukhe: the proof of LAW codemode_source_index_spelled

import Base
import ../../bend/codemode_source.bend as Src
import ../../bend/ffi_codemode_source.bend as FSrc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/codemode_source.bend as CodemodeSource
import ./base.bend as LACs

# PROOF of LAW codemode_source_index_spelled: the wire's Nat reader read the key and ',' whole (wire_nat_exact), below the cap; its spelling is the decimal one (wire_nat_decimal).

def CodemodeSource.codemode_source_index_spelled(k, n, e):
  LACs.csi.got(String.append(k, ","), Wr.get_nat(String.append(k, ",")), {==}, n, e)

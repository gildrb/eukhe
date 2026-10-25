# eukhe: the proof of LAW wire_u32_reads_decimal
#
# PROOF of LAW wire_u32_reads_decimal: the decimal spelling is put_u32's
# (wire_u32_decimal), which reads back (wire_u32_round_trip).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire

def Wire.wire_u32_reads_decimal(x, rest):
  +r = rest
  %Wire.wire_u32_decimal(x, r) : {Wr.get_u32(_) == Wr.Got{x, r} : Wr.Dec<U32>}
  Wire.wire_u32_round_trip(x, r)

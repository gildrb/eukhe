# eukhe: the proof of LAW wire_u32_decimal
#
# PROOF of LAW wire_u32_decimal: put_u32 is put_nat of the value, which is
# wire_dec (wire_nat_decimal).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire

def Wire.wire_u32_decimal(x, rest):
  Wire.wire_nat_decimal(U32.to_nat(x), rest)

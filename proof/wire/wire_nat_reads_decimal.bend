# eukhe: the proof of LAW wire_nat_reads_decimal
#
# PROOF of LAW wire_nat_reads_decimal: the decimal spelling is put_nat's
# (wire_nat_decimal), which reads back (wire_nat_round_trip).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire

def Wire.wire_nat_reads_decimal(n, rest, h):
  +r = rest
  %Wire.wire_nat_decimal(n, r) : {Wr.get_nat(_) == Wr.Got{n, r} : Wr.Dec<Nat>}
  Wire.wire_nat_round_trip(n, r, h)

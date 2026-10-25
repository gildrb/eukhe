# eukhe: the proof of LAW wire_str_reads_decimal
#
# PROOF of LAW wire_str_reads_decimal: the decimal spelling is put_str's
# (wire_str_decimal), which reads back (wire_str_round_trip).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire

def Wire.wire_str_reads_decimal(a, rest, h):
  +r = rest
  %Wire.wire_str_decimal(a, r) : {Wr.get_str(_) == Wr.Got{a, r} : Wr.Dec<String>}
  Wire.wire_str_round_trip(a, r, h)

# eukhe: the proof of LAW wire_nats_reads_decimal
#
# PROOF of LAW wire_nats_reads_decimal: the decimal spelling is put_list's
# (wire_nats_decimal), which reads back (wire_list_round_trip).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire

def Wire.wire_nats_reads_decimal(xs, rest, h):
  +r = rest
  %Wire.wire_nats_decimal(xs, r) : {Wr.get_list(~Nat, ~Wr.get_nat, _) == Wr.Got{xs, r} : Wr.Dec<List<&2, Nat>>}
  Wire.wire_list_round_trip(xs, r, h)

# eukhe: the proof of LAW wire_strs_reads_decimal
#
# PROOF of LAW wire_strs_reads_decimal: the decimal spelling is
# wire_spell_strs (wire_strs_spells, wire_strs_decimal), which reads back
# (wire_strs_round_trip).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire

def Wire.wire_strs_reads_decimal(xs, rest, h):
  +r = rest
  %Wire.wire_strs_decimal(xs, r) : {Wr.get_list(~String, ~Wr.get_str, _) == Wr.Got{xs, r} : Wr.Dec<List<&2, String>>}
  %Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, xs, r), LawsBase.wire_spell_strs(xs, r), Wire.wire_strs_spells(xs, r)) : {Wr.get_list(~String, ~Wr.get_str, _) == Wr.Got{xs, r} : Wr.Dec<List<&2, String>>}
  Wire.wire_strs_round_trip(xs, r, h)

# eukhe: the proof of LAW wire_strs_decimal
#
# PROOF of LAW wire_strs_decimal: put_list is wire_spell_strs
# (wire_strs_spells), whose count is put_nat (wire_nat_decimal) and whose
# items are put_str (wire_str_decimal; by induction, wsd_items).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire

def wsd_items(xs: List<&2, String>, +rest: String) -> {LawsBase.wire_spell_strs.items(xs, rest) == LawsBase.wire_dec_strs.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Wire.wire_str_decimal(x, LawsBase.wire_dec_strs.items(t, rest)) : {Wr.put_str(x, LawsBase.wire_spell_strs.items(t, rest)) == _ : String}
      %wsd_items(t, rest) : {Wr.put_str(x, LawsBase.wire_spell_strs.items(t, rest)) == Wr.put_str(x, _) : String}
      {==}

def Wire.wire_strs_decimal(xs, rest):
  +r = rest
  +l = List.length(&2, String, xs)
  %Wire.wire_nat_decimal(l, LawsBase.wire_dec_strs.items(xs, r)) : {Wr.put_list(~String, ~Wr.put_str, xs, r) == _ : String}
  %wsd_items(xs, r) : {Wr.put_list(~String, ~Wr.put_str, xs, r) == Wr.put_nat(l, _) : String}
  Wire.wire_strs_spells(xs, r)

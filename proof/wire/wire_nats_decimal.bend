# eukhe: the proof of LAW wire_nats_decimal
#
# PROOF of LAW wire_nats_decimal: put_list is wire_spell_nats
# (wire_nats_spells), whose count and items are put_nat, which is wire_dec
# (LAWireDec.wdec.nat; the items by induction, wnd_items).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./base/dec.bend as LAWireDec

def wnd_items(xs: List<&2, Nat>, +rest: String) -> {LawsBase.wire_spell_nats.items(xs, rest) == LawsBase.wire_dec_nats.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %LAWireDec.wdec.nat(x, LawsBase.wire_dec_nats.items(t, rest)) : {Wr.put_nat(x, LawsBase.wire_spell_nats.items(t, rest)) == _ : String}
      %wnd_items(t, rest) : {Wr.put_nat(x, LawsBase.wire_spell_nats.items(t, rest)) == Wr.put_nat(x, _) : String}
      {==}

def Wire.wire_nats_decimal(xs, rest):
  +r = rest
  +l = List.length(&2, Nat, xs)
  %LAWireDec.wdec.nat(l, LawsBase.wire_dec_nats.items(xs, r)) : {Wr.put_list(~Nat, ~Wr.put_nat, xs, r) == _ : String}
  %wnd_items(xs, r) : {Wr.put_list(~Nat, ~Wr.put_nat, xs, r) == Wr.put_nat(l, _) : String}
  Wire.wire_nats_spells(xs, r)

# eukhe: the proof of LAW wire_nats_spells
#
# PROOF of LAW wire_nats_spells: put_list's loop counts the Nats and
# spells each before the rest (induction on the list); fin puts the count
# in front, which is wire_spell_nats.

import Base
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../../laws/base.bend as LawsBase

# the loop: the count and the spelled items
def ws_nats_go(xs: List<&2, Nat>, -rest: String) -> {Wr.put_list.go(~Nat, ~Wr.put_nat, xs, rest) == (List.length(&2, Nat, xs), LawsBase.wire_spell_nats.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Nat, ~Wr.put_nat, t, rest), (List.length(&2, Nat, t), LawsBase.wire_spell_nats.items(t, rest)), ws_nats_go(t, rest)) : {Wr.put_list.step(~Nat, ~Wr.put_nat, x, _) == (1n+List.length(&2, Nat, t), Wr.put_nat(x, LawsBase.wire_spell_nats.items(t, rest))) : Nat & String}
      {==}

def Wire.wire_nats_spells(xs, rest):
  %Equal.sym(Nat & String, Wr.put_list.go(~Nat, ~Wr.put_nat, xs, rest), (List.length(&2, Nat, xs), LawsBase.wire_spell_nats.items(xs, rest)), ws_nats_go(xs, rest)) : {Wr.put_list.fin(_) == LawsBase.wire_spell_nats(xs, rest) : String}
  {==}

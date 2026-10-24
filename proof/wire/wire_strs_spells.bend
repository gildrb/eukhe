# eukhe: the proof of LAW wire_strs_spells
#
# PROOF of LAW wire_strs_spells: put_list's loop counts the strings and
# spells each before the rest (induction on the list); fin puts the count
# in front, which is wire_spell_strs.

import Base
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../../laws/base.bend as LawsBase

# the loop: the count and the spelled items
def ws_strs_go(xs: List<&2, String>, -rest: String) -> {Wr.put_list.go(~String, ~Wr.put_str, xs, rest) == (List.length(&2, String, xs), LawsBase.wire_spell_strs.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, t, rest), (List.length(&2, String, t), LawsBase.wire_spell_strs.items(t, rest)), ws_strs_go(t, rest)) : {Wr.put_list.step(~String, ~Wr.put_str, x, _) == (1n+List.length(&2, String, t), Wr.put_str(x, LawsBase.wire_spell_strs.items(t, rest))) : Nat & String}
      {==}

def Wire.wire_strs_spells(xs, rest):
  %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, xs, rest), (List.length(&2, String, xs), LawsBase.wire_spell_strs.items(xs, rest)), ws_strs_go(xs, rest)) : {Wr.put_list.fin(_) == LawsBase.wire_spell_strs(xs, rest) : String}
  {==}

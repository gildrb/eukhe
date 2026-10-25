# eukhe: the proof of LAW wire_strs_round_trip
#
# PROOF of LAW wire_strs_round_trip: the count fits, so it reads back
# (wire_nat_round_trip); then the item loop reads each string back
# (wire_str_round_trip), leaving the spelling of the next one, and the
# last leaves rest (induction on the list).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# the item loop reads back x then t
def ws_strs_go_rt(+t: List<&2, String>, +x: String, +rest: String, +hf: {LawsBase.wire_strs_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, t), Wr.get_str(Wr.put_str(x, LawsBase.wire_spell_strs.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, String>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(x)), True{}, hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, String>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, Wr.put_str(y, LawsBase.wire_spell_strs.items(u, rest)))), Wr.Got{x, Wr.put_str(y, LawsBase.wire_spell_strs.items(u, rest))}, Wire.wire_str_round_trip(x, Wr.put_str(y, LawsBase.wire_spell_strs.items(u, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(x)), LawsBase.wire_strs_all(y <> u), hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 1n+List.length(&2, String, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, u), Wr.get_str(Wr.put_str(y, LawsBase.wire_spell_strs.items(u, rest)))), Wr.Got{y <> u, rest}, ws_strs_go_rt(u, y, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(x)), LawsBase.wire_strs_all(y <> u), hf))) : {Wr.get_list.cons(String, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      {==}

def Wire.wire_strs_round_trip(xs, rest, h):
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {Wr.get_list.start(~String, ~Wr.get_str, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, String>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, String, x <> t), LawsBase.wire_spell_strs.items(x <> t, r))), Wr.Got{List.length(&2, String, x <> t), LawsBase.wire_spell_strs.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, String, x <> t), LawsBase.wire_spell_strs.items(x <> t, r), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, String, x <> t)), LawsBase.wire_strs_all(x <> t), hh))) : {Wr.get_list.start(~String, ~Wr.get_str, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, String>>}
      ws_strs_go_rt(t, x, r, LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, String, x <> t)), LawsBase.wire_strs_all(x <> t), hh))

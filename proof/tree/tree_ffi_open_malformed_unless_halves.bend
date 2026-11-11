# eukhe: the proof of LAW tree_ffi_open_malformed_unless_halves
#
# PROOF: the wire's list reader reads only a spelled list, then the rest
# (wire_list_exact), that fits the wire (TH.th.nats_fit); when it reads
# none the open answers the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tree.bend as Tree
import ../../laws/wire.bend as Wire
import ../wire/base/spell.bend as LAWireSpell
import ../wire/wire_list_exact.bend as PWireListExact
import ./base/halves.bend as TH

def mh.goal(input: String) -> Type:
  &hs: List<&2, Nat> -> &rest: String -> {(input, Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs))) == (Wr.put_list(~Nat, ~Wr.put_nat, hs, rest), True{}) : String & Bool}

def mh.eq(+input: String, +hs: List<&2, Nat>, +rest: String, e1: {input == Wr.put_list(~Nat, ~Wr.put_nat, hs, rest) : String}, e2: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)) == True{} : Bool}) -> {(input, Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs))) == (Wr.put_list(~Nat, ~Wr.put_nat, hs, rest), True{}) : String & Bool}:
  %Equal.sym(String, input, Wr.put_list(~Nat, ~Wr.put_nat, hs, rest), e1) : {(_, Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs))) == (Wr.put_list(~Nat, ~Wr.put_nat, hs, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)), True{}, e2) : {(Wr.put_list(~Nat, ~Wr.put_nat, hs, rest), _) == (Wr.put_list(~Nat, ~Wr.put_nat, hs, rest), True{}) : String & Bool}
  {==}

def mh.main(+input: String, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, input) == d : Wr.Dec<List<&2, Nat>>}, other: {String.eq(Pair.snd(Ft.St, String, Ft.open.go(d)), Wr.err("tree: malformed halves")) == False{} : Bool}) -> mh.goal(input):
  match d:
    case Wr.Got{+hs, +rest}:
      +e = ed
      (hs, (rest, mh.eq(input, hs, rest, Wire.wire_list_exact(input, hs, rest, e), TH.th.nats_fit(input, hs, rest, e))))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(mh.goal(input), other)

def Tree.tree_ffi_open_malformed_unless_halves(input, other):
  mh.main(input, Wr.get_list(~Nat, ~Wr.get_nat, input), {==}, other)

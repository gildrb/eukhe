# eukhe: the proof of LAW tree_ffi_open_reads_only_halves
#
# PROOF: a list the wire's list reader reads is exactly its spelling, then
# the rest (wire_list_exact), and fits the wire (TH.th.nats_fit); the open
# answers no error only for such a list read whole, nothing left (the
# other branches answer the error form, which the premise excludes), and
# then opens the empty core at those halves.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tree.bend as Tree
import ../../laws/wire.bend as Wire
import ../wire/base/spell.bend as LAWireSpell
import ../wire/wire_list_exact.bend as PWireListExact
import ./base/halves.bend as TH

def oh.G(input: String, out: Ft.St & String) -> Type:
  &hs: List<&2, Nat> -> {(input, (Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)), out)) == (Wr.put_list(~Nat, ~Wr.put_nat, hs, ""), (True{}, (Ft.Live{Tr.core.start(hs)}, ""))) : String & (Bool & (Ft.St & String))}

def oh.eq(+input: String, +hs: List<&2, Nat>, e: {input == Wr.put_list(~Nat, ~Wr.put_nat, hs, "") : String}, f: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)) == True{} : Bool}) -> {(input, (Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)), (Ft.Live{Tr.core.start(hs)}, ""))) == (Wr.put_list(~Nat, ~Wr.put_nat, hs, ""), (True{}, (Ft.Live{Tr.core.start(hs)}, ""))) : String & (Bool & (Ft.St & String))}:
  %Equal.sym(String, input, Wr.put_list(~Nat, ~Wr.put_nat, hs, ""), e) : {(_, (Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)), (Ft.Live{Tr.core.start(hs)}, ""))) == (Wr.put_list(~Nat, ~Wr.put_nat, hs, ""), (True{}, (Ft.Live{Tr.core.start(hs)}, ""))) : String & (Bool & (Ft.St & String))}
  %Equal.sym(Bool, Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)), True{}, f) : {(Wr.put_list(~Nat, ~Wr.put_nat, hs, ""), (_, (Ft.Live{Tr.core.start(hs)}, ""))) == (Wr.put_list(~Nat, ~Wr.put_nat, hs, ""), (True{}, (Ft.Live{Tr.core.start(hs)}, ""))) : String & (Bool & (Ft.St & String))}
  {==}

# the end check: nothing left opens the core, anything left is the error
# form
def oh.end(+input: String, +hs: List<&2, Nat>, r: String, ed: {Wr.get_list(~Nat, ~Wr.get_nat, input) == Wr.Got{hs, r} : Wr.Dec<List<&2, Nat>>}, ok: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.open.end(Wr.end(r), hs))) == False{} : Bool}) -> oh.G(input, Ft.open.end(Wr.end(r), hs)):
  match r:
    case SNil{}:
      +e = ed
      (hs, oh.eq(input, hs, Wire.wire_list_exact(input, hs, "", e), TH.th.nats_fit(input, hs, "", e)))
    case SCon{c, t}:
      LAWireSpell.ws_absurd(oh.G(input, Ft.open.end(False{}, hs)), ok)

def oh.main(+input: String, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, input) == d : Wr.Dec<List<&2, Nat>>}, ok: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.open.go(d))) == False{} : Bool}) -> oh.G(input, Ft.open.go(d)):
  match d:
    case Wr.Got{+hs, +r}:
      oh.end(input, hs, r, ed, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(oh.G(input, (Ft.Shut{}, Wr.err("tree: malformed halves"))), ok)

def Tree.tree_ffi_open_reads_only_halves(input, ok):
  oh.main(input, Wr.get_list(~Nat, ~Wr.get_nat, input), {==}, ok)

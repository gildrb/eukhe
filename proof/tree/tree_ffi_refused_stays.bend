# eukhe: the proof of LAW tree_ffi_refused_stays
#
# PROOF: an open answers the error form only when it is refused (the open
# of halves read whole answers nothing, no error: the premise excludes it);
# the refused state answers every step with the refusal and stays refused
# (rs.go, by induction on the inputs).

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tree.bend as Tree
import ../wire/base/spell.bend as LAWireSpell

# from the refused state, every step is refused
def rs.go(ins: List<&2, String>, +x: String) -> {Tree.tree.trace(ins, (Ft.Shut{}, x)) == x <> Tree.tree.refusals(ins) : List<&2, String>}:
  match ins:
    case Nil{}:
      {==}
    case i <> rest:
      +E = Wr.err("tree: the open was refused")
      %rs.go(rest, E) : {x <> Tree.tree.trace(rest, (Ft.Shut{}, E)) == x <> _ : List<&2, String>}
      {==}

def rs.end(r: String, -hs: List<&2, Nat>, bad: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.open.end(Wr.end(r), hs))) == True{} : Bool}, +ins: List<&2, String>) -> {Tree.tree.trace(ins, Ft.open.end(Wr.end(r), hs)) == Pair.snd(Ft.St, String, Ft.open.end(Wr.end(r), hs)) <> Tree.tree.refusals(ins) : List<&2, String>}:
  match r:
    case SNil{}:
      LAWireSpell.ws_absurd({Tree.tree.trace(ins, Ft.open.end(True{}, hs)) == Pair.snd(Ft.St, String, Ft.open.end(True{}, hs)) <> Tree.tree.refusals(ins) : List<&2, String>}, Equal.sym(Bool, False{}, True{}, bad))
    case SCon{c, t}:
      rs.go(ins, Wr.err("tree: input left after the halves"))

def rs.open(d: Wr.Dec<List<&2, Nat>>, bad: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.open.go(d))) == True{} : Bool}, +ins: List<&2, String>) -> {Tree.tree.trace(ins, Ft.open.go(d)) == Pair.snd(Ft.St, String, Ft.open.go(d)) <> Tree.tree.refusals(ins) : List<&2, String>}:
  match d:
    case Wr.Got{hs, r}:
      rs.end(r, hs, bad, ins)
    case Wr.Bad{}:
      rs.go(ins, Wr.err("tree: malformed halves"))

def Tree.tree_ffi_refused_stays(input, bad, ins):
  rs.open(Wr.get_list(~Nat, ~Wr.get_nat, input), bad, ins)

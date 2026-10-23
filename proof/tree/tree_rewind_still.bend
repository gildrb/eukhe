# eukhe: the proof of LAW tree_rewind_still

import Base
import ../../bend/tree.bend as Tr
import ../../laws/tree.bend as Tree
import ../base/bool/and.bend as LBoolAnd
import ./base/bool.bend as LABool
import ./base/logic.bend as LALogic
import ./base/tree/get.bend as LATreeGet
import ./base/tree/has.bend as LATreeHas

def pt.dels_nil(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, hit: Bool, eh: {Tr.held.at(s, b) == hit : Bool}, +ah: {LABool.pt.allhas(s, b) == True{} : Bool}) -> {Tr.dels.go(s, b, hit) == Nil{} : List<&2, Tr.Op>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +i = Tr.has(b, Tr.Ent.k(e))
          pt.dels_nil(r, b, Tr.held.at(r, b), {==}, LBoolAnd.tree.pt.and_r(i, LABool.pt.allhas(r, b), ah))
        case False{}:
          +i = Tr.has(b, Tr.Ent.k(e))
          LALogic.pt.void({Tr.dels.go(e <> r, b, False{}) == Nil{} : List<&2, Tr.Op>}, LABool.pt.flip(i, LBoolAnd.tree.pt.and_l(i, LABool.pt.allhas(r, b), ah), eh))

def pt.puts_nil(+a: List<&2, Tr.Ent>, s: List<&2, Tr.Ent>, hit: Bool, eh: {Tr.kept.at(a, s) == hit : Bool}, +w: {Tr.within(s, a) == True{} : Bool}) -> {Tr.puts.go(a, s, hit) == Nil{} : List<&2, Tr.Op>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +i = Tr.same(Tr.get(a, Tr.Ent.k(e)), Some{e})
          pt.puts_nil(a, r, Tr.kept.at(a, r), {==}, LBoolAnd.tree.pt.and_r(i, Tr.within(r, a), w))
        case False{}:
          +i = Tr.same(Tr.get(a, Tr.Ent.k(e)), Some{e})
          LALogic.pt.void({Tr.puts.go(a, e <> r, False{}) == Nil{} : List<&2, Tr.Op>}, LABool.pt.flip(i, LBoolAnd.tree.pt.and_l(i, Tr.within(r, a), w), eh))

def rewind_still(+a: List<&2, Tr.Ent>, ga: {Tr.sorted(a) == True{} : Bool}) -> {Tr.diff(a, a) == Nil{} : List<&2, Tr.Op>}:
  %Equal.sym(List<&2, Tr.Op>, Tr.dels(a, a), Nil{}, pt.dels_nil(a, a, Tr.held.at(a, a), {==}, LATreeHas.pt.allhas_self(a))) : {List.append(&2, Tr.Op, _, Tr.puts(a, a)) == Nil{} : List<&2, Tr.Op>}
  pt.puts_nil(a, a, Tr.kept.at(a, a), {==}, LATreeGet.pt.within_self(a, ga))

def Tree.tree_rewind_still(a, ga):
  rewind_still(a, ga)

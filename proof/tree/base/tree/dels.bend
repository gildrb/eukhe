# eukhe: lemmas the proofs of area tree share: tree/dels

import Base
import ../../../../bend/tree.bend as Tr
import ../logic.bend as LALogic
import ../nat.bend as LANat

def pt.dels_none(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, hit: Bool, +x: Nat) -> {LALogic.pt.look(Tr.dels.go(s, b, hit), None{}, x) == None{} : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          pt.dels_none(r, b, Tr.held.at(r, b), x)
        case False{}:
          +c = Nat.is_eq(Tr.Ent.k(e), x)
          %Equal.sym(Maybe<&2, Tr.Ent>, LALogic.tree.pt.pick(c, None{}, None{}), None{}, LALogic.pt.pick_same(c, None{})) : {LALogic.pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), _, x) == None{} : Maybe<&2, Tr.Ent>}
          pt.dels_none(r, b, Tr.held.at(r, b), x)

# the dels leave a key the target holds
def pt.dels_keep(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, hit: Bool, eh: {Tr.held.at(s, b) == hit : Bool}, +m: Maybe<&2, Tr.Ent>, +x: Nat, +hb: {Tr.has(b, x) == True{} : Bool}) -> {LALogic.pt.look(Tr.dels.go(s, b, hit), m, x) == m : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          pt.dels_keep(r, b, Tr.held.at(r, b), {==}, m, x, hb)
        case False{}:
          +ne = LANat.pt.ne_by(Tr.Ent.k(e), x, z => Tr.has(b, z), eh, hb)
          %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, ne) : {LALogic.pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), LALogic.tree.pt.pick(_, None{}, m), x) == m : Maybe<&2, Tr.Ent>}
          pt.dels_keep(r, b, Tr.held.at(r, b), {==}, m, x, hb)

# eukhe: lemmas the proofs of area tree share: tree/Ent

import Base
import ../../../../bend/tree.bend as Tr
import ../nat.bend as LANat

# Nodes
# -----

def pt.ent_eta(e: Tr.Ent) -> {Tr.Ent{Tr.Ent.k(e), Tr.Ent.p(e), Tr.Ent.v(e)} == e : Tr.Ent}:
  match e:
    case Tr.Ent{k, p, v}:
      {==}

def pt.ent_refl(e: Tr.Ent) -> {Tr.Ent.eq(e, e) == True{} : Bool}:
  match e:
    case Tr.Ent{+k, +p, +v}:
      %LANat.pt.eq_refl(k) : {Bool.and(_, Bool.and(Nat.is_eq(p, p), Nat.is_eq(v, v))) == True{} : Bool}
      %LANat.pt.eq_refl(p) : {Bool.and(True{}, Bool.and(_, Nat.is_eq(v, v))) == True{} : Bool}
      %LANat.pt.eq_refl(v) : {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}
      {==}

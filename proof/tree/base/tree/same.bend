# eukhe: lemmas the proofs of area tree share: tree/same

import Base
import ../../../../bend/tree.bend as Tr
import ./Ent.bend as LATreeEnt

def pt.same_refl(+e: Tr.Ent) -> {Tr.same(Some{e}, Some{e}) == True{} : Bool}:
  LATreeEnt.pt.ent_refl(e)

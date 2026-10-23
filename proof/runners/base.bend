# eukhe: lemmas the proofs of area runners share

import Base
import ../../LAWS.bend as Laws

# ---- runners ----

# proof_runners: the lemmas PROOF.bend proves the (G4) laws with
# (LAWS.bend section runners), about the model in bend/runners.bend.

# Logic
# -----

def pr.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pr.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pr.BD(_, A, Unit)
  Unit{}

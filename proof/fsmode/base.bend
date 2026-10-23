# eukhe: lemmas the proofs of area fsmode share

import Base

def fsmode.pf.BD(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

def fsmode.pf.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : fsmode.pf.BD(_, A)
  Unit{}

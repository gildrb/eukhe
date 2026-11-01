# eukhe: lemmas shared by the proofs of area job_notice: a refuted
# premise proves anything

import Base

def jnb.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def jnb.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a premise False == True proves anything
def jnb.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : jnb.IfF(_, G)
  Unit{}

# a premise True == False proves anything
def jnb.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : jnb.IfT(_, G)
  Unit{}

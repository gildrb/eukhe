# eukhe: lemmas the proofs of area dash share

import Base

# Logic
# -----

def dashboard_auth.pa.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def dashboard_auth.pa.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : dashboard_auth.pa.BD(_, A, Unit)
  Unit{}

def dashboard_auth.pa.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : dashboard_auth.pa.BD(_, Unit, A)
  Unit{}

# ---- dash entry ----

# Bool.and, for the fits of the dash entry's requests
def pe.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def pe.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      dashboard_auth.pa.absurdF({b == True{} : Bool}, h)

def pe.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

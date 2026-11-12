# eukhe: lemmas the proofs of area dash share

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash

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

# ---- dash choices ----

# a presented token checked against a file that holds one: Rust's report
# decides
def pa.check_some(m: Maybe<&2, List<&2, Nat>>, +b: Bool, e: {Dash.sp_has(m) == True{} : Bool}) -> {Da.check(m, b) == Da.pass.matches(b) : Da.Pass}:
  match m:
    case None{}:
      dashboard_auth.pa.absurdF({Da.check(None{}, b) == Da.pass.matches(b) : Da.Pass}, e)
    case Some{bs}:
      {==}

# a presented token checked against a file that holds none: refused
def pa.check_none(m: Maybe<&2, List<&2, Nat>>, +b: Bool, e: {Dash.sp_has(m) == False{} : Bool}) -> {Da.check(m, b) == Da.Refuse{Da.unset()} : Da.Pass}:
  match m:
    case None{}:
      {==}
    case Some{bs}:
      dashboard_auth.pa.absurdT({Da.check(Some{bs}, b) == Da.Refuse{Da.unset()} : Da.Pass}, e)

# the start choice on a file that holds a token is the mode's
def pa.held_some(m: Maybe<&2, List<&2, Nat>>, +mode: Nat, e: {Dash.sp_has(m) == True{} : Bool}) -> {Da.keep.held(m, mode) == Da.keep.mode(mode) : Da.Keep}:
  match m:
    case None{}:
      dashboard_auth.pa.absurdF({Da.keep.held(None{}, mode) == Da.keep.mode(mode) : Da.Keep}, e)
    case Some{bs}:
      {==}

# the start choice on a file that holds no token: tokenless
def pa.held_none(m: Maybe<&2, List<&2, Nat>>, +mode: Nat, e: {Dash.sp_has(m) == False{} : Bool}) -> {Da.keep.held(m, mode) == Da.Tokenless{} : Da.Keep}:
  match m:
    case None{}:
      {==}
    case Some{bs}:
      dashboard_auth.pa.absurdT({Da.keep.held(Some{bs}, mode) == Da.Tokenless{} : Da.Keep}, e)

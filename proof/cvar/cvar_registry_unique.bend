# eukhe: the proof of LAW cvar_registry_unique

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ../base.bend as L
import ./base.bend as LA

def pv.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LA.pv.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pv.not_f(+b: Bool, h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

def pv.eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pv.eq_comm(p, q)

def pv.ne_comm(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  %pv.eq_comm(a, b) : {_ == False{} : Bool}
  h

# The registry
# ------------

# a lookup that misses a list misses its head
def pv.find_ne(b: Bool, +h: Cv.Decl, +r: List<&2, Cv.Decl>, +y: Nat, nf: {Maybe.is_some(&2, Cv.Decl, Cv.find.go(h <> r, y, b)) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      nf
    case False{}:
      {==}

# a lookup that misses a list misses its tail
def pv.find_tail(b: Bool, +h: Cv.Decl, +r: List<&2, Cv.Decl>, +y: Nat, nf: {Maybe.is_some(&2, Cv.Decl, Cv.find.go(h <> r, y, b)) == False{} : Bool}) -> {Maybe.is_some(&2, Cv.Decl, Cv.find(r, y)) == False{} : Bool}:
  match b:
    case True{}:
      L.cvar.pv.absurd({Maybe.is_some(&2, Cv.Decl, Cv.find(r, y)) == False{} : Bool}, nf)
    case False{}:
      nf

# a lookup that misses ds misses ds with another id appended
def pv.find_snoc(r: List<&2, Cv.Decl>, +d: Cv.Decl, +y: Nat, b: Bool, eb: {Cv.id.at(r, y) == b : Bool}, h1: {Maybe.is_some(&2, Cv.Decl, Cv.find.go(r, y, b)) == False{} : Bool}, h2: {Nat.is_eq(Cv.Decl.id(d), y) == False{} : Bool}) -> {Maybe.is_some(&2, Cv.Decl, Cv.find(List.append(&2, Cv.Decl, r, [d]), y)) == False{} : Bool}:
  match r:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(Cv.Decl.id(d), y), False{}, h2) : {Maybe.is_some(&2, Cv.Decl, Cv.find.go([d], y, _)) == False{} : Bool}
      {==}
    case +h <> +t:
      match b:
        case True{}:
          L.cvar.pv.absurd({Maybe.is_some(&2, Cv.Decl, Cv.find(h <> List.append(&2, Cv.Decl, t, [d]), y)) == False{} : Bool}, h1)
        case False{}:
          %Equal.sym(Bool, Nat.is_eq(Cv.Decl.id(h), y), False{}, eb) : {Maybe.is_some(&2, Cv.Decl, Cv.find.go(h <> List.append(&2, Cv.Decl, t, [d]), y, _)) == False{} : Bool}
          pv.find_snoc(t, d, y, Cv.id.at(t, y), {==}, h1, h2)

def pv.unique_snoc(ds: List<&2, Cv.Decl>, +d: Cv.Decl, +h: {Cv.unique(ds) == True{} : Bool}, +nf: {Maybe.is_some(&2, Cv.Decl, Cv.find(ds, Cv.Decl.id(d))) == False{} : Bool}) -> {Cv.unique(List.append(&2, Cv.Decl, ds, [d])) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +x <> +r:
      +nx = Bool.not(Maybe.is_some(&2, Cv.Decl, Cv.find(r, Cv.Decl.id(x))))
      +ne = pv.find_ne(Nat.is_eq(Cv.Decl.id(x), Cv.Decl.id(d)), x, r, Cv.Decl.id(d), nf)
      +nr = pv.find_tail(Nat.is_eq(Cv.Decl.id(x), Cv.Decl.id(d)), x, r, Cv.Decl.id(d), nf)
      +hx = pv.not_t(Maybe.is_some(&2, Cv.Decl, Cv.find(r, Cv.Decl.id(x))), LA.cvar.pv.and_l(nx, Cv.unique(r), h))
      +hr = LA.cvar.pv.and_r(nx, Cv.unique(r), h)
      +rd = List.append(&2, Cv.Decl, r, [d])
      +fs = pv.find_snoc(r, d, Cv.Decl.id(x), Cv.id.at(r, Cv.Decl.id(x)), {==}, hx, pv.ne_comm(Cv.Decl.id(x), Cv.Decl.id(d), ne))
      LA.pv.and_t(Bool.not(Maybe.is_some(&2, Cv.Decl, Cv.find(rd, Cv.Decl.id(x)))), Cv.unique(rd), pv.not_f(Maybe.is_some(&2, Cv.Decl, Cv.find(rd, Cv.Decl.id(x))), fs), pv.unique_snoc(r, d, hr, nr))

def pv.declare_unique(t: Bool, g: Bool, +ds: List<&2, Cv.Decl>, +d: Cv.Decl, et: {Maybe.is_some(&2, Cv.Decl, Cv.find(ds, Cv.Decl.id(d))) == t : Bool}, h: {Cv.unique(ds) == True{} : Bool}) -> {Cv.unique(Cv.declare.at(t, g, ds, d)) == True{} : Bool}:
  match t:
    case True{}:
      h
    case False{}:
      match g:
        case True{}:
          pv.unique_snoc(ds, d, h, et)
        case False{}:
          h

def pv.reg_unique(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, h: {Cv.unique(ds) == True{} : Bool}) -> {Cv.unique(Cv.registry.go(xs, ds)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +d <> rest:
      pv.reg_unique(rest, Cv.declare(ds, d), pv.declare_unique(Maybe.is_some(&2, Cv.Decl, Cv.find(ds, Cv.Decl.id(d))), Cv.Decl.typed(d), ds, d, {==}, h))

# The laws
# --------

def pv.cvar_registry_unique(xs: List<&2, Cv.Decl>) -> {Cv.unique(Cv.registry(xs)) == True{} : Bool}:
  pv.reg_unique(xs, Nil{}, {==})

# (S4) Settings as console variables

def Cvar.cvar_registry_unique(xs):
  pv.cvar_registry_unique(xs)

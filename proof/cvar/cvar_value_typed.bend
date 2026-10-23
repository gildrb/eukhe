# eukhe: the proof of LAW cvar_value_typed

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base.bend as LA

def pv.MD(m: Maybe<&2, Cv.Decl>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

def pv.none_some(-A: Type, -d: Cv.Decl, e: {None{} == Some{d} : Maybe<&2, Cv.Decl>}) -> A:
  %e : pv.MD(_, Unit, A)
  Unit{}

def pv.some_inj(-a: Cv.Decl, -b: Cv.Decl, e: {Some{a} == Some{b} : Maybe<&2, Cv.Decl>}) -> {a == b : Cv.Decl}:
  Equal.cong(Maybe<&2, Cv.Decl>, Cv.Decl, m => Maybe.default(&2, Cv.Decl, m, a), Some{a}, Some{b}, e)

def pv.ty_refl(t: Cv.Ty) -> {Cv.Ty.eq(t, t) == True{} : Bool}:
  match t:
    case Cv.TNat{}:
      {==}
    case Cv.TBool{}:
      {==}

def pv.ty_true(a: Cv.Ty, b: Cv.Ty, h: {Cv.Ty.eq(a, b) == True{} : Bool}) -> {a == b : Cv.Ty}:
  match a b:
    case Cv.TNat{} Cv.TNat{}:
      {==}
    case Cv.TNat{} Cv.TBool{}:
      LA.pv.absurdF({Cv.TNat{} == Cv.TBool{} : Cv.Ty}, h)
    case Cv.TBool{} Cv.TNat{}:
      LA.pv.absurdF({Cv.TBool{} == Cv.TNat{} : Cv.Ty}, h)
    case Cv.TBool{} Cv.TBool{}:
      {==}

# the declaration found in a typed list is typed
def pv.find_typed(ds: List<&2, Cv.Decl>, +x: Nat, b: Bool, +d: Cv.Decl, em: {Cv.find.go(ds, x, b) == Some{d} : Maybe<&2, Cv.Decl>}, +at: {Cv.all_typed(ds) == True{} : Bool}) -> {Cv.Decl.typed(d) == True{} : Bool}:
  match ds:
    case Nil{}:
      pv.none_some({Cv.Decl.typed(d) == True{} : Bool}, d, em)
    case +h <> +r:
      match b:
        case True{}:
          %pv.some_inj(h, d, em) : {Cv.Decl.typed(_) == True{} : Bool}
          LA.cvar.pv.and_l(Cv.Decl.typed(h), Cv.all_typed(r), at)
        case False{}:
          pv.find_typed(r, x, Cv.id.at(r, x), d, em, LA.cvar.pv.and_r(Cv.Decl.typed(h), Cv.all_typed(r), at))

def pv.init_ty(d: Cv.Decl, h: {Cv.Decl.typed(d) == True{} : Bool}) -> {Cv.Val.ty(Cv.Decl.init(d)) == Cv.Decl.ty(d) : Cv.Ty}:
  match d:
    case Cv.Decl{i, t, s, p, r, v}:
      pv.ty_true(Cv.Val.ty(v), t, h)

def pv.valid_ty(l: Cv.Layer, +d: Cv.Decl, +s: Cv.Bind, h: {Cv.valid.at(Some{d}, l, s) == True{} : Bool}) -> {Cv.Ty.eq(Cv.Val.ty(Cv.Bind.val(s)), Cv.Decl.ty(d)) == True{} : Bool}:
  match l:
    case Cv.Config{}:
      h
    case Cv.Agent{}:
      LA.cvar.pv.and_r(Cv.Decl.local(d), Cv.Ty.eq(Cv.Val.ty(Cv.Bind.val(s)), Cv.Decl.ty(d)), h)

# a set that hits x has the type of x's declaration
def pv.hit_ty(+s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +d: Cv.Decl, em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, +h: {Cv.hit.at([s], ds, l, x) == True{} : Bool}) -> {Cv.Ty.eq(Cv.Val.ty(Cv.Bind.val(s)), Cv.Decl.ty(d)) == True{} : Bool}:
  +ex = LA.pv.eq_true(Cv.Bind.id(s), x, LA.cvar.pv.and_l(Nat.is_eq(Cv.Bind.id(s), x), Cv.valid(ds, l, s), h))
  +hv = LA.cvar.pv.and_r(Nat.is_eq(Cv.Bind.id(s), x), Cv.valid(ds, l, s), h)
  pv.valid_ty(l, d, s, LA.pv.valid_m(ds, l, s, x, Some{d}, em, ex, hv))

# the value is absent or has type t
def pv.mty(m: Maybe<&2, Cv.Val>, t: Cv.Ty) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{y}:
      Cv.Ty.eq(Cv.Val.ty(y), t)

def pv.step_ty(b: Bool, +s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +d: Cv.Decl, +cur: Maybe<&2, Cv.Val>, em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, eb: {Cv.hit.at([s], ds, l, x) == b : Bool}, hc: {pv.mty(cur, Cv.Decl.ty(d)) == True{} : Bool}) -> {pv.mty(Cv.layer.go([s], ds, l, x, cur, b), Cv.Decl.ty(d)) == True{} : Bool}:
  match b:
    case True{}:
      pv.hit_ty(s, ds, l, x, d, em, eb)
    case False{}:
      hc

# every layer keeps the type of x's declaration
def pv.layer_ty(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +d: Cv.Decl, +cur: Maybe<&2, Cv.Val>, +em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, hc: {pv.mty(cur, Cv.Decl.ty(d)) == True{} : Bool}) -> {pv.mty(Cv.layer(ss, ds, l, x, cur), Cv.Decl.ty(d)) == True{} : Bool}:
  match ss:
    case Nil{}:
      hc
    case +s <> +r:
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> r, ds, l, x, cur), Cv.layer(r, ds, l, x, Cv.layer([s], ds, l, x, cur)), LA.pv.layer_cons(s, r, ds, l, x, cur)) : {pv.mty(_, Cv.Decl.ty(d)) == True{} : Bool}
      pv.layer_ty(r, ds, l, x, d, Cv.layer([s], ds, l, x, cur), em, pv.step_ty(Cv.hit.at([s], ds, l, x), s, ds, l, x, d, cur, em, {==}, hc))

def pv.def_ty(m: Maybe<&2, Cv.Val>, +b: Cv.Val, +t: Cv.Ty, hm: {pv.mty(m, t) == True{} : Bool}, hb: {Cv.Val.ty(b) == t : Cv.Ty}) -> {Cv.Val.ty(Maybe.default(&2, Cv.Val, m, b)) == t : Cv.Ty}:
  match m:
    case None{}:
      hb
    case Some{y}:
      pv.ty_true(Cv.Val.ty(y), t, hm)

def pv.over_ty(+ds: List<&2, Cv.Decl>, +a: Cv.Ag, +x: Nat, +d: Cv.Decl, +b: Cv.Val, +em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, hb: {Cv.Val.ty(b) == Cv.Decl.ty(d) : Cv.Ty}) -> {Cv.Val.ty(Cv.over(ds, a, x, b)) == Cv.Decl.ty(d) : Cv.Ty}:
  +q = Cv.layer(Cv.Ag.profile(a), ds, Cv.Agent{}, x, None{})
  +hq = pv.layer_ty(Cv.Ag.profile(a), ds, Cv.Agent{}, x, d, None{}, em, {==})
  pv.def_ty(Cv.layer(Cv.Ag.sets(a), ds, Cv.Agent{}, x, q), b, Cv.Decl.ty(d), pv.layer_ty(Cv.Ag.sets(a), ds, Cv.Agent{}, x, d, q, em, hq), hb)

def pv.chain_ty(fam: List<&2, Cv.Ag>, +ds: List<&2, Cv.Decl>, +x: Nat, +d: Cv.Decl, +b: Cv.Val, +em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, hb: {Cv.Val.ty(b) == Cv.Decl.ty(d) : Cv.Ty}) -> {Cv.Val.ty(Cv.chain(fam, ds, x, b)) == Cv.Decl.ty(d) : Cv.Ty}:
  match fam:
    case Nil{}:
      hb
    case +a <> r:
      pv.chain_ty(r, ds, x, d, Cv.over(ds, a, x, b), em, pv.over_ty(ds, a, x, d, b, em, hb))

def pv.vt_m(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat, +em: {Cv.find(ds, x) == m : Maybe<&2, Cv.Decl>}, at: {Cv.all_typed(ds) == True{} : Bool}) -> {Cv.typed.at(m, Cv.value.at(m, ds, cfg, fam, x)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      +r = Cv.root.val(ds, cfg, x, d)
      +hi = pv.init_ty(d, pv.find_typed(ds, x, Cv.id.at(ds, x), d, em, at))
      +hr = pv.def_ty(Cv.layer(cfg, ds, Cv.Config{}, x, None{}), Cv.Decl.init(d), Cv.Decl.ty(d), pv.layer_ty(cfg, ds, Cv.Config{}, x, d, None{}, em, {==}), hi)
      +hc = pv.chain_ty(fam, ds, x, d, r, em, hr)
      %Equal.sym(Cv.Ty, Cv.Val.ty(Cv.chain(fam, ds, x, r)), Cv.Decl.ty(d), hc) : {Cv.Ty.eq(_, Cv.Decl.ty(d)) == True{} : Bool}
      pv.ty_refl(Cv.Decl.ty(d))

def pv.cvar_value_typed(+xs: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.typed.at(Cv.find(Cv.registry(xs), x), Cv.value(Cv.registry(xs), cfg, fam, x)) == True{} : Bool}:
  pv.vt_m(Cv.find(Cv.registry(xs), x), Cv.registry(xs), cfg, fam, x, {==}, LA.pv.cvar_registry_typed(xs))

def Cvar.cvar_value_typed(xs, cfg, fam, x):
  pv.cvar_value_typed(xs, cfg, fam, x)

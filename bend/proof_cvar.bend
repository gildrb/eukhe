# proof_cvar: the S4 laws (docs/harness.md) of the cvar model in
# bend/cvar.bend.
#
# A layer of sets is read one set at a time (`pv.layer_cons`), so a set
# appended last acts on the value of the sets before it
# (`pv.layer_snoc`): a hit gives its value, a miss keeps the value.
# The registry adds a declaration only when its id is free and its
# default is well typed, which keeps it unique and typed; a hit is a
# valid set of the found declaration, so every layer keeps the type of
# the default. A set of a Global cvar never hits in an agent layer. The
# cfg an agent writes drops only sets that miss its persisted cvar. A
# toggle's set of x hits or misses the same way whatever its Bool, so
# a second toggle undoes the first. Expansion leaves only plain
# commands, and its depth bound turns a self-running alias into a
# cycle.

import Base
import ./cvar.bend as Cv

# Logic
# -----

def pv.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pv.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pv.BD(_, Unit, A)
  Unit{}

def pv.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pv.BD(_, A, Unit)
  Unit{}

def pv.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pv.absurdF({False{} == True{} : Bool}, h)

def pv.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pv.absurdF({b == True{} : Bool}, h)

def pv.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pv.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      pv.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pv.not_f(+b: Bool, h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

def pv.not_not(b: Bool) -> {Bool.not(Bool.not(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

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

# Numbers and types
# -----------------

def pv.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pv.eq_refl(p)

def pv.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pv.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pv.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pv.eq_true(p, q, h))

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
      pv.absurdF({Cv.TNat{} == Cv.TBool{} : Cv.Ty}, h)
    case Cv.TBool{} Cv.TNat{}:
      pv.absurdF({Cv.TBool{} == Cv.TNat{} : Cv.Ty}, h)
    case Cv.TBool{} Cv.TBool{}:
      {==}

# Lists
# -----

def pv.app_nil(xs: List<&2, Cv.Cmd>) -> {List.append(&2, Cv.Cmd, xs, Nil{}) == xs : List<&2, Cv.Cmd>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, Cv.Cmd>, List<&2, Cv.Cmd>, z => h <> z, List.append(&2, Cv.Cmd, t, Nil{}), t, pv.app_nil(t))

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
      pv.absurd({Maybe.is_some(&2, Cv.Decl, Cv.find(r, y)) == False{} : Bool}, nf)
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
          pv.absurd({Maybe.is_some(&2, Cv.Decl, Cv.find(h <> List.append(&2, Cv.Decl, t, [d]), y)) == False{} : Bool}, h1)
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
      +hx = pv.not_t(Maybe.is_some(&2, Cv.Decl, Cv.find(r, Cv.Decl.id(x))), pv.and_l(nx, Cv.unique(r), h))
      +hr = pv.and_r(nx, Cv.unique(r), h)
      +rd = List.append(&2, Cv.Decl, r, [d])
      +fs = pv.find_snoc(r, d, Cv.Decl.id(x), Cv.id.at(r, Cv.Decl.id(x)), {==}, hx, pv.ne_comm(Cv.Decl.id(x), Cv.Decl.id(d), ne))
      pv.and_t(Bool.not(Maybe.is_some(&2, Cv.Decl, Cv.find(rd, Cv.Decl.id(x)))), Cv.unique(rd), pv.not_f(Maybe.is_some(&2, Cv.Decl, Cv.find(rd, Cv.Decl.id(x))), fs), pv.unique_snoc(r, d, hr, nr))

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

def pv.all_typed_snoc(ds: List<&2, Cv.Decl>, +d: Cv.Decl, +h: {Cv.all_typed(ds) == True{} : Bool}, g: {Cv.Decl.typed(d) == True{} : Bool}) -> {Cv.all_typed(List.append(&2, Cv.Decl, ds, [d])) == True{} : Bool}:
  match ds:
    case Nil{}:
      %Equal.sym(Bool, Cv.Decl.typed(d), True{}, g) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case +x <> +r:
      pv.and_t(Cv.Decl.typed(x), Cv.all_typed(List.append(&2, Cv.Decl, r, [d])), pv.and_l(Cv.Decl.typed(x), Cv.all_typed(r), h), pv.all_typed_snoc(r, d, pv.and_r(Cv.Decl.typed(x), Cv.all_typed(r), h), g))

def pv.declare_typed(t: Bool, g: Bool, +ds: List<&2, Cv.Decl>, +d: Cv.Decl, eg: {Cv.Decl.typed(d) == g : Bool}, h: {Cv.all_typed(ds) == True{} : Bool}) -> {Cv.all_typed(Cv.declare.at(t, g, ds, d)) == True{} : Bool}:
  match t:
    case True{}:
      h
    case False{}:
      match g:
        case True{}:
          pv.all_typed_snoc(ds, d, h, eg)
        case False{}:
          h

def pv.reg_typed(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, h: {Cv.all_typed(ds) == True{} : Bool}) -> {Cv.all_typed(Cv.registry.go(xs, ds)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +d <> rest:
      pv.reg_typed(rest, Cv.declare(ds, d), pv.declare_typed(Maybe.is_some(&2, Cv.Decl, Cv.find(ds, Cv.Decl.id(d))), Cv.Decl.typed(d), ds, d, {==}, h))

# the declaration found in a typed list is typed
def pv.find_typed(ds: List<&2, Cv.Decl>, +x: Nat, b: Bool, +d: Cv.Decl, em: {Cv.find.go(ds, x, b) == Some{d} : Maybe<&2, Cv.Decl>}, +at: {Cv.all_typed(ds) == True{} : Bool}) -> {Cv.Decl.typed(d) == True{} : Bool}:
  match ds:
    case Nil{}:
      pv.none_some({Cv.Decl.typed(d) == True{} : Bool}, d, em)
    case +h <> +r:
      match b:
        case True{}:
          %pv.some_inj(h, d, em) : {Cv.Decl.typed(_) == True{} : Bool}
          pv.and_l(Cv.Decl.typed(h), Cv.all_typed(r), at)
        case False{}:
          pv.find_typed(r, x, Cv.id.at(r, x), d, em, pv.and_r(Cv.Decl.typed(h), Cv.all_typed(r), at))

def pv.init_ty(d: Cv.Decl, h: {Cv.Decl.typed(d) == True{} : Bool}) -> {Cv.Val.ty(Cv.Decl.init(d)) == Cv.Decl.ty(d) : Cv.Ty}:
  match d:
    case Cv.Decl{i, t, s, p, r, v}:
      pv.ty_true(Cv.Val.ty(v), t, h)

# Layers
# ------

def pv.layer_cons_go(b: Bool, +s: Cv.Bind, +r: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer.go(s <> r, ds, l, x, cur, b) == Cv.layer(r, ds, l, x, Cv.layer.go([s], ds, l, x, cur, b)) : Maybe<&2, Cv.Val>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a layer reads its first set, then the rest
def pv.layer_cons(+s: Cv.Bind, +r: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer(s <> r, ds, l, x, cur) == Cv.layer(r, ds, l, x, Cv.layer([s], ds, l, x, cur)) : Maybe<&2, Cv.Val>}:
  pv.layer_cons_go(Cv.hit.at([s], ds, l, x), s, r, ds, l, x, cur)

# a layer reads its last set on the value of the sets before it
def pv.layer_snoc(ss: List<&2, Cv.Bind>, +s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer(List.append(&2, Cv.Bind, ss, [s]), ds, l, x, cur) == Cv.layer([s], ds, l, x, Cv.layer(ss, ds, l, x, cur)) : Maybe<&2, Cv.Val>}:
  match ss:
    case Nil{}:
      {==}
    case +h <> +r:
      +c1 = Cv.layer([h], ds, l, x, cur)
      +rs = List.append(&2, Cv.Bind, r, [s])
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(h <> r, ds, l, x, cur), Cv.layer(r, ds, l, x, c1), pv.layer_cons(h, r, ds, l, x, cur)) : {Cv.layer(h <> rs, ds, l, x, cur) == Cv.layer([s], ds, l, x, _) : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(h <> rs, ds, l, x, cur), Cv.layer(rs, ds, l, x, c1), pv.layer_cons(h, rs, ds, l, x, cur)) : {_ == Cv.layer([s], ds, l, x, Cv.layer(r, ds, l, x, c1)) : Maybe<&2, Cv.Val>}
      pv.layer_snoc(r, s, ds, l, x, c1)

def pv.layer_hit(+s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>, h: {Cv.hit.at([s], ds, l, x) == True{} : Bool}) -> {Cv.layer([s], ds, l, x, cur) == Some{Cv.Bind.val(s)} : Maybe<&2, Cv.Val>}:
  %Equal.sym(Bool, Cv.hit.at([s], ds, l, x), True{}, h) : {Cv.layer.go([s], ds, l, x, cur, _) == Some{Cv.Bind.val(s)} : Maybe<&2, Cv.Val>}
  {==}

def pv.layer_miss(+s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>, h: {Cv.hit.at([s], ds, l, x) == False{} : Bool}) -> {Cv.layer([s], ds, l, x, cur) == cur : Maybe<&2, Cv.Val>}:
  %Equal.sym(Bool, Cv.hit.at([s], ds, l, x), False{}, h) : {Cv.layer.go([s], ds, l, x, cur, _) == cur : Maybe<&2, Cv.Val>}
  {==}

# a valid set of x is valid under the declaration found for x
def pv.valid_m(+ds: List<&2, Cv.Decl>, l: Cv.Layer, +s: Cv.Bind, +x: Nat, m: Maybe<&2, Cv.Decl>, em: {Cv.find(ds, x) == m : Maybe<&2, Cv.Decl>}, ex: {Cv.Bind.id(s) == x : Nat}, h: {Cv.valid(ds, l, s) == True{} : Bool}) -> {Cv.valid.at(m, l, s) == True{} : Bool}:
  %em : {Cv.valid.at(_, l, s) == True{} : Bool}
  %ex : {Cv.valid.at(Cv.find(ds, _), l, s) == True{} : Bool}
  h

def pv.valid_ty(l: Cv.Layer, +d: Cv.Decl, +s: Cv.Bind, h: {Cv.valid.at(Some{d}, l, s) == True{} : Bool}) -> {Cv.Ty.eq(Cv.Val.ty(Cv.Bind.val(s)), Cv.Decl.ty(d)) == True{} : Bool}:
  match l:
    case Cv.Config{}:
      h
    case Cv.Agent{}:
      pv.and_r(Cv.Decl.local(d), Cv.Ty.eq(Cv.Val.ty(Cv.Bind.val(s)), Cv.Decl.ty(d)), h)

# a set that hits x has the type of x's declaration
def pv.hit_ty(+s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +d: Cv.Decl, em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, +h: {Cv.hit.at([s], ds, l, x) == True{} : Bool}) -> {Cv.Ty.eq(Cv.Val.ty(Cv.Bind.val(s)), Cv.Decl.ty(d)) == True{} : Bool}:
  +ex = pv.eq_true(Cv.Bind.id(s), x, pv.and_l(Nat.is_eq(Cv.Bind.id(s), x), Cv.valid(ds, l, s), h))
  +hv = pv.and_r(Nat.is_eq(Cv.Bind.id(s), x), Cv.valid(ds, l, s), h)
  pv.valid_ty(l, d, s, pv.valid_m(ds, l, s, x, Some{d}, em, ex, hv))

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
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> r, ds, l, x, cur), Cv.layer(r, ds, l, x, Cv.layer([s], ds, l, x, cur)), pv.layer_cons(s, r, ds, l, x, cur)) : {pv.mty(_, Cv.Decl.ty(d)) == True{} : Bool}
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

# Chains
# ------

def pv.chain_snoc(fam: List<&2, Cv.Ag>, +a: Cv.Ag, +ds: List<&2, Cv.Decl>, +x: Nat, +b: Cv.Val) -> {Cv.chain(List.append(&2, Cv.Ag, fam, [a]), ds, x, b) == Cv.over(ds, a, x, Cv.chain(fam, ds, x, b)) : Cv.Val}:
  match fam:
    case Nil{}:
      {==}
    case +h <> r:
      pv.chain_snoc(r, a, ds, x, Cv.over(ds, h, x, b))

def pv.inh_m(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.value.at(m, ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{Nil{}, Nil{}}]), x) == Cv.value.at(m, ds, cfg, fam, x) : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      +r = Cv.root.val(ds, cfg, x, d)
      Equal.cong(Cv.Val, Maybe<&2, Cv.Val>, y => Some{y}, Cv.chain(List.append(&2, Cv.Ag, fam, [Cv.Ag{Nil{}, Nil{}}]), ds, x, r), Cv.chain(fam, ds, x, r), pv.chain_snoc(fam, Cv.Ag{Nil{}, Nil{}}, ds, x, r))

# the set of x to v hits x when it is valid
def pv.hit_self(+ds: List<&2, Cv.Decl>, +x: Nat, +v: Cv.Val, ok: {Cv.valid(ds, Cv.Agent{}, Cv.Bind{x, v}) == True{} : Bool}) -> {Cv.hit.at([Cv.Bind{x, v}], ds, Cv.Agent{}, x) == True{} : Bool}:
  %pv.eq_refl(x) : {Bool.and(_, Cv.valid(ds, Cv.Agent{}, Cv.Bind{x, v})) == True{} : Bool}
  ok

def pv.sw_m(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, +v: Cv.Val, em: {Cv.find(ds, x) == m : Maybe<&2, Cv.Decl>}, +ok: {Cv.valid(ds, Cv.Agent{}, Cv.Bind{x, v}) == True{} : Bool}) -> {Cv.value.at(m, ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, List.append(&2, Cv.Bind, ss, [Cv.Bind{x, v}])}]), x) == Some{v} : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      pv.absurdF({None{} == Some{v} : Maybe<&2, Cv.Val>}, pv.valid_m(ds, Cv.Agent{}, Cv.Bind{x, v}, x, None{}, em, {==}, ok))
    case Some{+d}:
      +r = Cv.root.val(ds, cfg, x, d)
      +ag = {Cv.Ag{p, List.append(&2, Cv.Bind, ss, [Cv.Bind{x, v}])} : Cv.Ag}
      +c = Cv.chain(fam, ds, x, r)
      +lp = Cv.layer(p, ds, Cv.Agent{}, x, None{})
      +q = Cv.layer(ss, ds, Cv.Agent{}, x, lp)
      %Equal.sym(Cv.Val, Cv.chain(List.append(&2, Cv.Ag, fam, [ag]), ds, x, r), Cv.over(ds, ag, x, c), pv.chain_snoc(fam, ag, ds, x, r)) : {Some{_} == Some{v} : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, ss, [Cv.Bind{x, v}]), ds, Cv.Agent{}, x, lp), Cv.layer([Cv.Bind{x, v}], ds, Cv.Agent{}, x, q), pv.layer_snoc(ss, Cv.Bind{x, v}, ds, Cv.Agent{}, x, lp)) : {Some{Maybe.default(&2, Cv.Val, _, c)} == Some{v} : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer([Cv.Bind{x, v}], ds, Cv.Agent{}, x, q), Some{v}, pv.layer_hit(Cv.Bind{x, v}, ds, Cv.Agent{}, x, q, pv.hit_self(ds, x, v, ok))) : {Some{Maybe.default(&2, Cv.Val, _, c)} == Some{v} : Maybe<&2, Cv.Val>}
      {==}

# Global cvars
# ------------

def pv.global_miss(b: Bool, +s: Cv.Bind, +ds: List<&2, Cv.Decl>, +x: Nat, +d: Cv.Decl, eb: {Nat.is_eq(Cv.Bind.id(s), x) == b : Bool}, em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, gl: {Cv.Decl.local(d) == False{} : Bool}) -> {Bool.and(b, Cv.valid(ds, Cv.Agent{}, s)) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, Cv.Bind.id(s), x, pv.eq_true(Cv.Bind.id(s), x, eb)) : {Cv.valid.at(Cv.find(ds, _), Cv.Agent{}, s) == False{} : Bool}
      %Equal.sym(Maybe<&2, Cv.Decl>, Cv.find(ds, x), Some{d}, em) : {Cv.valid.at(_, Cv.Agent{}, s) == False{} : Bool}
      %Equal.sym(Bool, Cv.Decl.local(d), False{}, gl) : {Bool.and(_, Cv.Ty.eq(Cv.Val.ty(Cv.Bind.val(s)), Cv.Decl.ty(d))) == False{} : Bool}
      {==}
    case False{}:
      {==}

# no agent layer changes a Global cvar
def pv.layer_global(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +x: Nat, +d: Cv.Decl, +cur: Maybe<&2, Cv.Val>, +em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, +gl: {Cv.Decl.local(d) == False{} : Bool}) -> {Cv.layer(ss, ds, Cv.Agent{}, x, cur) == cur : Maybe<&2, Cv.Val>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +r:
      +c1 = Cv.layer([s], ds, Cv.Agent{}, x, cur)
      +miss = pv.global_miss(Nat.is_eq(Cv.Bind.id(s), x), s, ds, x, d, {==}, em, gl)
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> r, ds, Cv.Agent{}, x, cur), Cv.layer(r, ds, Cv.Agent{}, x, c1), pv.layer_cons(s, r, ds, Cv.Agent{}, x, cur)) : {_ == cur : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, c1, cur, pv.layer_miss(s, ds, Cv.Agent{}, x, cur, miss)) : {Cv.layer(r, ds, Cv.Agent{}, x, _) == cur : Maybe<&2, Cv.Val>}
      pv.layer_global(r, ds, x, d, cur, em, gl)

def pv.over_global(+ds: List<&2, Cv.Decl>, +a: Cv.Ag, +x: Nat, +d: Cv.Decl, +b: Cv.Val, +em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, +gl: {Cv.Decl.local(d) == False{} : Bool}) -> {Cv.over(ds, a, x, b) == b : Cv.Val}:
  +lp = Cv.layer(Cv.Ag.profile(a), ds, Cv.Agent{}, x, None{})
  %Equal.sym(Maybe<&2, Cv.Val>, lp, None{}, pv.layer_global(Cv.Ag.profile(a), ds, x, d, None{}, em, gl)) : {Maybe.default(&2, Cv.Val, Cv.layer(Cv.Ag.sets(a), ds, Cv.Agent{}, x, _), b) == b : Cv.Val}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(Cv.Ag.sets(a), ds, Cv.Agent{}, x, None{}), None{}, pv.layer_global(Cv.Ag.sets(a), ds, x, d, None{}, em, gl)) : {Maybe.default(&2, Cv.Val, _, b) == b : Cv.Val}
  {==}

def pv.chain_global(fam: List<&2, Cv.Ag>, +ds: List<&2, Cv.Decl>, +x: Nat, +d: Cv.Decl, +b: Cv.Val, +em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, +gl: {Cv.Decl.local(d) == False{} : Bool}) -> {Cv.chain(fam, ds, x, b) == b : Cv.Val}:
  match fam:
    case Nil{}:
      {==}
    case +a <> r:
      Equal.trans(Cv.Val, Cv.chain(r, ds, x, Cv.over(ds, a, x, b)), Cv.over(ds, a, x, b), b, pv.chain_global(r, ds, x, d, Cv.over(ds, a, x, b), em, gl), pv.over_global(ds, a, x, d, b, em, gl))

def pv.gu(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat, +d: Cv.Decl, +found: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, +gl: {Cv.Decl.local(d) == False{} : Bool}) -> {Cv.value(ds, cfg, fam, x) == Some{Cv.root.val(ds, cfg, x, d)} : Maybe<&2, Cv.Val>}:
  +r = Cv.root.val(ds, cfg, x, d)
  %Equal.sym(Maybe<&2, Cv.Decl>, Cv.find(ds, x), Some{d}, found) : {Cv.value.at(_, ds, cfg, fam, x) == Some{r} : Maybe<&2, Cv.Val>}
  Equal.cong(Cv.Val, Maybe<&2, Cv.Val>, y => Some{y}, Cv.chain(fam, ds, x, r), r, pv.chain_global(fam, ds, x, d, r, found, gl))

# Written sets
# ------------

def pv.wf(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag, hit: Bool, eh: {Cv.out.at(ss, ds, f) == hit : Bool}) -> {Cv.all_flag(Cv.written.go(ss, ds, f, hit), ds, f) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      match hit:
        case True{}:
          +w = Cv.written.go(rest, ds, f, Cv.out.at(rest, ds, f))
          +fl = Cv.flag.at(Cv.find(ds, Cv.Bind.id(s)), f)
          pv.and_t(fl, Cv.all_flag(w, ds, f), pv.and_l(fl, Cv.valid(ds, Cv.Agent{}, s), eh), pv.wf(rest, ds, f, Cv.out.at(rest, ds, f), {==}))
        case False{}:
          pv.wf(rest, ds, f, Cv.out.at(rest, ds, f), {==})

def pv.wf_top(+ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag) -> {Cv.all_flag(Cv.written(ss, ds, f), ds, f) == True{} : Bool}:
  pv.wf(ss, ds, f, Cv.out.at(ss, ds, f), {==})

# a set that hits a persisted cvar is written
def pv.out_hit(+s: Cv.Bind, +ds: List<&2, Cv.Decl>, +x: Nat, keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}, +h: {Cv.hit.at([s], ds, Cv.Agent{}, x) == True{} : Bool}) -> {Cv.out.at([s], ds, Cv.Persist{}) == True{} : Bool}:
  +ex = pv.eq_true(Cv.Bind.id(s), x, pv.and_l(Nat.is_eq(Cv.Bind.id(s), x), Cv.valid(ds, Cv.Agent{}, s), h))
  +hv = pv.and_r(Nat.is_eq(Cv.Bind.id(s), x), Cv.valid(ds, Cv.Agent{}, s), h)
  %Equal.sym(Nat, Cv.Bind.id(s), x, ex) : {Bool.and(Cv.flag.at(Cv.find(ds, _), Cv.Persist{}), Cv.valid(ds, Cv.Agent{}, s)) == True{} : Bool}
  pv.and_t(Cv.flag.at(Cv.find(ds, x), Cv.Persist{}), Cv.valid(ds, Cv.Agent{}, s), keeps, hv)

# a set that is not written misses a persisted cvar
def pv.out_miss(b: Bool, +s: Cv.Bind, +ds: List<&2, Cv.Decl>, +x: Nat, keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}, eb: {Cv.hit.at([s], ds, Cv.Agent{}, x) == b : Bool}, ho: {Cv.out.at([s], ds, Cv.Persist{}) == False{} : Bool}) -> {Cv.hit.at([s], ds, Cv.Agent{}, x) == False{} : Bool}:
  match b:
    case True{}:
      pv.absurd({Cv.hit.at([s], ds, Cv.Agent{}, x) == False{} : Bool}, Equal.trans(Bool, True{}, Cv.out.at([s], ds, Cv.Persist{}), False{}, Equal.sym(Bool, Cv.out.at([s], ds, Cv.Persist{}), True{}, pv.out_hit(s, ds, x, keeps, eb)), ho))
    case False{}:
      eb

# the written sets give every persisted cvar the value of all sets
def pv.persist_go(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +x: Nat, +keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}, +cur: Maybe<&2, Cv.Val>, ho: Bool, eho: {Cv.out.at(ss, ds, Cv.Persist{}) == ho : Bool}) -> {Cv.layer(Cv.written.go(ss, ds, Cv.Persist{}, ho), ds, Cv.Agent{}, x, cur) == Cv.layer(ss, ds, Cv.Agent{}, x, cur) : Maybe<&2, Cv.Val>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      match ho:
        case True{}:
          +w = Cv.written.go(rest, ds, Cv.Persist{}, Cv.out.at(rest, ds, Cv.Persist{}))
          +c1 = Cv.layer([s], ds, Cv.Agent{}, x, cur)
          %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> rest, ds, Cv.Agent{}, x, cur), Cv.layer(rest, ds, Cv.Agent{}, x, c1), pv.layer_cons(s, rest, ds, Cv.Agent{}, x, cur)) : {Cv.layer(s <> w, ds, Cv.Agent{}, x, cur) == _ : Maybe<&2, Cv.Val>}
          %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> w, ds, Cv.Agent{}, x, cur), Cv.layer(w, ds, Cv.Agent{}, x, c1), pv.layer_cons(s, w, ds, Cv.Agent{}, x, cur)) : {_ == Cv.layer(rest, ds, Cv.Agent{}, x, c1) : Maybe<&2, Cv.Val>}
          pv.persist_go(rest, ds, x, keeps, c1, Cv.out.at(rest, ds, Cv.Persist{}), {==})
        case False{}:
          +w = Cv.written.go(rest, ds, Cv.Persist{}, Cv.out.at(rest, ds, Cv.Persist{}))
          +c1 = Cv.layer([s], ds, Cv.Agent{}, x, cur)
          +miss = pv.out_miss(Cv.hit.at([s], ds, Cv.Agent{}, x), s, ds, x, keeps, {==}, eho)
          %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> rest, ds, Cv.Agent{}, x, cur), Cv.layer(rest, ds, Cv.Agent{}, x, c1), pv.layer_cons(s, rest, ds, Cv.Agent{}, x, cur)) : {Cv.layer(w, ds, Cv.Agent{}, x, cur) == _ : Maybe<&2, Cv.Val>}
          %Equal.sym(Maybe<&2, Cv.Val>, c1, cur, pv.layer_miss(s, ds, Cv.Agent{}, x, cur, miss)) : {Cv.layer(w, ds, Cv.Agent{}, x, cur) == Cv.layer(rest, ds, Cv.Agent{}, x, _) : Maybe<&2, Cv.Val>}
          pv.persist_go(rest, ds, x, keeps, cur, Cv.out.at(rest, ds, Cv.Persist{}), {==})

def pv.pr_m(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}) -> {Cv.value.at(m, ds, cfg, [Cv.Ag{Cv.written(ss, ds, Cv.Persist{}), Nil{}}], x) == Cv.value.at(m, ds, cfg, [Cv.Ag{Nil{}, ss}], x) : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      +r = Cv.root.val(ds, cfg, x, d)
      Equal.cong(Maybe<&2, Cv.Val>, Maybe<&2, Cv.Val>, z => Some{Maybe.default(&2, Cv.Val, z, r)}, Cv.layer(Cv.written(ss, ds, Cv.Persist{}), ds, Cv.Agent{}, x, None{}), Cv.layer(ss, ds, Cv.Agent{}, x, None{}), pv.persist_go(ss, ds, x, keeps, None{}, Cv.out.at(ss, ds, Cv.Persist{}), {==}))

# Toggle
# ------

def pv.G_some(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +a: Cv.Ag, +x: Nat, +d: Cv.Decl, em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) == Some{Cv.over(ds, a, x, Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d)))} : Maybe<&2, Cv.Val>}:
  +r = Cv.root.val(ds, cfg, x, d)
  %Equal.sym(Maybe<&2, Cv.Decl>, Cv.find(ds, x), Some{d}, em) : {Cv.value.at(_, ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) == Some{Cv.over(ds, a, x, Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d)))} : Maybe<&2, Cv.Val>}
  Equal.cong(Cv.Val, Maybe<&2, Cv.Val>, y => Some{y}, Cv.chain(List.append(&2, Cv.Ag, fam, [a]), ds, x, r), Cv.over(ds, a, x, Cv.chain(fam, ds, x, r)), pv.chain_snoc(fam, a, ds, x, r))

def pv.T_eq(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +a: Cv.Ag, +x: Nat, +d: Cv.Decl, em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, +y: Cv.Val, ey: {Cv.over(ds, a, x, Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d))) == y : Cv.Val}) -> {Cv.toggle(ds, cfg, fam, a, x) == Cv.add(a, Cv.flip(x, Some{y})) : Cv.Ag}:
  +o = Cv.over(ds, a, x, Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d)))
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x), Some{o}, pv.G_some(ds, cfg, fam, a, x, d, em)) : {Cv.add(a, Cv.flip(x, _)) == Cv.add(a, Cv.flip(x, Some{y})) : Cv.Ag}
  %Equal.sym(Cv.Val, o, y, ey) : {Cv.add(a, Cv.flip(x, Some{_})) == Cv.add(a, Cv.flip(x, Some{y})) : Cv.Ag}
  {==}

def pv.O_snoc_miss(+ds: List<&2, Cv.Decl>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +s: Cv.Bind, +x: Nat, +r: Cv.Val, h: {Cv.hit.at([s], ds, Cv.Agent{}, x) == False{} : Bool}) -> {Cv.over(ds, Cv.Ag{p, List.append(&2, Cv.Bind, ss, [s])}, x, r) == Cv.over(ds, Cv.Ag{p, ss}, x, r) : Cv.Val}:
  +q = Cv.layer(p, ds, Cv.Agent{}, x, None{})
  +c = Cv.layer(ss, ds, Cv.Agent{}, x, q)
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, ss, [s]), ds, Cv.Agent{}, x, q), Cv.layer([s], ds, Cv.Agent{}, x, c), pv.layer_snoc(ss, s, ds, Cv.Agent{}, x, q)) : {Maybe.default(&2, Cv.Val, _, r) == Cv.over(ds, Cv.Ag{p, ss}, x, r) : Cv.Val}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer([s], ds, Cv.Agent{}, x, c), c, pv.layer_miss(s, ds, Cv.Agent{}, x, c, h)) : {Maybe.default(&2, Cv.Val, _, r) == Cv.over(ds, Cv.Ag{p, ss}, x, r) : Cv.Val}
  {==}

def pv.O_snoc_hit(+ds: List<&2, Cv.Decl>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +s: Cv.Bind, +x: Nat, +r: Cv.Val, h: {Cv.hit.at([s], ds, Cv.Agent{}, x) == True{} : Bool}) -> {Cv.over(ds, Cv.Ag{p, List.append(&2, Cv.Bind, ss, [s])}, x, r) == Cv.Bind.val(s) : Cv.Val}:
  +q = Cv.layer(p, ds, Cv.Agent{}, x, None{})
  +c = Cv.layer(ss, ds, Cv.Agent{}, x, q)
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, ss, [s]), ds, Cv.Agent{}, x, q), Cv.layer([s], ds, Cv.Agent{}, x, c), pv.layer_snoc(ss, s, ds, Cv.Agent{}, x, q)) : {Maybe.default(&2, Cv.Val, _, r) == Cv.Bind.val(s) : Cv.Val}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer([s], ds, Cv.Agent{}, x, c), Some{Cv.Bind.val(s)}, pv.layer_hit(s, ds, Cv.Agent{}, x, c, h)) : {Maybe.default(&2, Cv.Val, _, r) == Cv.Bind.val(s) : Cv.Val}
  {==}

# a Bool set of x is valid whatever its Bool
def pv.vb_at(m: Maybe<&2, Cv.Decl>, +x: Nat, +c1: Bool, +c2: Bool) -> {Cv.valid.at(m, Cv.Agent{}, Cv.Bind{x, Cv.VBool{c1}}) == Cv.valid.at(m, Cv.Agent{}, Cv.Bind{x, Cv.VBool{c2}}) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      {==}

def pv.vb_hit(+ds: List<&2, Cv.Decl>, +x: Nat, +c1: Bool, +c2: Bool) -> {Cv.hit.at([Cv.Bind{x, Cv.VBool{c1}}], ds, Cv.Agent{}, x) == Cv.hit.at([Cv.Bind{x, Cv.VBool{c2}}], ds, Cv.Agent{}, x) : Bool}:
  Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(x, x), z), Cv.valid.at(Cv.find(ds, x), Cv.Agent{}, Cv.Bind{x, Cv.VBool{c1}}), Cv.valid.at(Cv.find(ds, x), Cv.Agent{}, Cv.Bind{x, Cv.VBool{c2}}), pv.vb_at(Cv.find(ds, x), x, c1, c2))

# the second toggle of a Bool cvar, after the first hit or missed
def pv.tog_b(w: Bool, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, +d: Cv.Decl, +em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, +b: Bool, +ew: {Cv.hit.at([Cv.Bind{x, Cv.VBool{Bool.not(b)}}], ds, Cv.Agent{}, x) == w : Bool}, +ey: {Cv.over(ds, Cv.Ag{p, ss}, x, Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d))) == Cv.VBool{b} : Cv.Val}) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.Ag{p, List.append(&2, Cv.Bind, ss, [Cv.Bind{x, Cv.VBool{Bool.not(b)}}])}, x)]), x) == Some{Cv.VBool{b}} : Maybe<&2, Cv.Val>}:
  match w:
    case True{}:
      +r = Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d))
      +b1 = {Cv.Bind{x, Cv.VBool{Bool.not(b)}} : Cv.Bind}
      +b2 = {Cv.Bind{x, Cv.VBool{Bool.not(Bool.not(b))}} : Cv.Bind}
      +s1 = List.append(&2, Cv.Bind, ss, [b1])
      +a1 = {Cv.Ag{p, s1} : Cv.Ag}
      +a2 = {Cv.Ag{p, List.append(&2, Cv.Bind, s1, [b2])} : Cv.Ag}
      +e2 = pv.T_eq(ds, cfg, fam, a1, x, d, em, Cv.VBool{Bool.not(b)}, pv.O_snoc_hit(ds, p, ss, b1, x, r, ew))
      +h2 = Equal.trans(Bool, Cv.hit.at([b2], ds, Cv.Agent{}, x), Cv.hit.at([b1], ds, Cv.Agent{}, x), True{}, pv.vb_hit(ds, x, Bool.not(Bool.not(b)), Bool.not(b)), ew)
      %Equal.sym(Cv.Ag, Cv.toggle(ds, cfg, fam, a1, x), a2, e2) : {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [_]), x) == Some{Cv.VBool{b}} : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a2]), x), Some{Cv.over(ds, a2, x, r)}, pv.G_some(ds, cfg, fam, a2, x, d, em)) : {_ == Some{Cv.VBool{b}} : Maybe<&2, Cv.Val>}
      %Equal.sym(Cv.Val, Cv.over(ds, a2, x, r), Cv.Bind.val(b2), pv.O_snoc_hit(ds, p, s1, b2, x, r, h2)) : {Some{_} == Some{Cv.VBool{b}} : Maybe<&2, Cv.Val>}
      %Equal.sym(Bool, Bool.not(Bool.not(b)), b, pv.not_not(b)) : {Some{Cv.VBool{_}} == Some{Cv.VBool{b}} : Maybe<&2, Cv.Val>}
      {==}
    case False{}:
      +r = Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d))
      +b1 = {Cv.Bind{x, Cv.VBool{Bool.not(b)}} : Cv.Bind}
      +s1 = List.append(&2, Cv.Bind, ss, [b1])
      +a1 = {Cv.Ag{p, s1} : Cv.Ag}
      +a2 = {Cv.Ag{p, List.append(&2, Cv.Bind, s1, [b1])} : Cv.Ag}
      +o1 = Equal.trans(Cv.Val, Cv.over(ds, a1, x, r), Cv.over(ds, Cv.Ag{p, ss}, x, r), Cv.VBool{b}, pv.O_snoc_miss(ds, p, ss, b1, x, r, ew), ey)
      +e2 = pv.T_eq(ds, cfg, fam, a1, x, d, em, Cv.VBool{b}, o1)
      +o2 = Equal.trans(Cv.Val, Cv.over(ds, a2, x, r), Cv.over(ds, a1, x, r), Cv.VBool{b}, pv.O_snoc_miss(ds, p, s1, b1, x, r, ew), o1)
      %Equal.sym(Cv.Ag, Cv.toggle(ds, cfg, fam, a1, x), a2, e2) : {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [_]), x) == Some{Cv.VBool{b}} : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a2]), x), Some{Cv.over(ds, a2, x, r)}, pv.G_some(ds, cfg, fam, a2, x, d, em)) : {_ == Some{Cv.VBool{b}} : Maybe<&2, Cv.Val>}
      Equal.cong(Cv.Val, Maybe<&2, Cv.Val>, y => Some{y}, Cv.over(ds, a2, x, r), Cv.VBool{b}, o2)

# two toggles of a declared cvar, by the type of its value
def pv.tog_y(y: Cv.Val, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, +d: Cv.Decl, +em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, +ey: {Cv.over(ds, Cv.Ag{p, ss}, x, Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d))) == y : Cv.Val}) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.toggle(ds, cfg, fam, Cv.Ag{p, ss}, x), x)]), x) == Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), x) : Maybe<&2, Cv.Val>}:
  match y:
    case Cv.VNat{+n}:
      +a = {Cv.Ag{p, ss} : Cv.Ag}
      +e1 = pv.T_eq(ds, cfg, fam, a, x, d, em, Cv.VNat{n}, ey)
      %Equal.sym(Cv.Ag, Cv.toggle(ds, cfg, fam, a, x), a, e1) : {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, _, x)]), x) == Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) : Maybe<&2, Cv.Val>}
      %Equal.sym(Cv.Ag, Cv.toggle(ds, cfg, fam, a, x), a, e1) : {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [_]), x) == Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) : Maybe<&2, Cv.Val>}
      {==}
    case Cv.VBool{+b}:
      +a = {Cv.Ag{p, ss} : Cv.Ag}
      +r = Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d))
      +a1 = {Cv.Ag{p, List.append(&2, Cv.Bind, ss, [Cv.Bind{x, Cv.VBool{Bool.not(b)}}])} : Cv.Ag}
      +e1 = pv.T_eq(ds, cfg, fam, a, x, d, em, Cv.VBool{b}, ey)
      %Equal.sym(Cv.Ag, Cv.toggle(ds, cfg, fam, a, x), a1, e1) : {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, _, x)]), x) == Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x), Some{Cv.over(ds, a, x, r)}, pv.G_some(ds, cfg, fam, a, x, d, em)) : {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, a1, x)]), x) == _ : Maybe<&2, Cv.Val>}
      %Equal.sym(Cv.Val, Cv.over(ds, a, x, r), Cv.VBool{b}, ey) : {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, a1, x)]), x) == Some{_} : Maybe<&2, Cv.Val>}
      pv.tog_b(Cv.hit.at([Cv.Bind{x, Cv.VBool{Bool.not(b)}}], ds, Cv.Agent{}, x), ds, cfg, fam, p, ss, x, d, em, b, {==}, ey)

def pv.tog_m(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, +em: {Cv.find(ds, x) == m : Maybe<&2, Cv.Decl>}) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.toggle(ds, cfg, fam, Cv.Ag{p, ss}, x), x)]), x) == Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), x) : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, Cv.Decl>, Cv.find(ds, x), None{}, em) : {Cv.value.at(_, ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.toggle(ds, cfg, fam, Cv.Ag{p, ss}, x), x)]), x) == Cv.value.at(_, ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, ss}]), x) : Maybe<&2, Cv.Val>}
      {==}
    case Some{+d}:
      pv.tog_y(Cv.over(ds, Cv.Ag{p, ss}, x, Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d))), ds, cfg, fam, p, ss, x, d, em, {==})

# Aliases
# -------

def pv.plain_app(xs: List<&2, Cv.Cmd>, +ys: List<&2, Cv.Cmd>, hx: {Cv.plain(xs) == True{} : Bool}, hy: {Cv.plain(ys) == True{} : Bool}) -> {Cv.plain(List.append(&2, Cv.Cmd, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case c <> rest:
      match c:
        case Cv.CSet{i, v}:
          pv.plain_app(rest, ys, hx, hy)
        case Cv.CToggle{i}:
          pv.plain_app(rest, ys, hx, hy)
        case Cv.CRun{n}:
          hx
        case Cv.CGone{n}:
          hx

def pv.plain_cat(a: Cv.Exp, b: Cv.Exp, ha: {Cv.Exp.plain(a) == True{} : Bool}, hb: {Cv.Exp.plain(b) == True{} : Bool}) -> {Cv.Exp.plain(Cv.cat(a, b)) == True{} : Bool}:
  match a:
    case Cv.Flat{x}:
      match b:
        case Cv.Flat{y}:
          pv.plain_app(x, y, ha, hb)
        case Cv.Cycle{}:
          {==}
        case Cv.Unknown{}:
          {==}
    case Cv.Cycle{}:
      {==}
    case Cv.Unknown{}:
      {==}

def pv.ex_plain(d: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> {Cv.Exp.plain(Cv.expand.go(d, cs, as)) == True{} : Bool}:
  match d:
    case 0n:
      match cs:
        case Nil{}:
          {==}
        case c <> +rest:
          match c:
            case Cv.CSet{i, v}:
              pv.plain_cat(Cv.Flat{[Cv.CSet{i, v}]}, Cv.expand.go(0n, rest, as), {==}, pv.ex_plain(0n, rest, as))
            case Cv.CToggle{i}:
              pv.plain_cat(Cv.Flat{[Cv.CToggle{i}]}, Cv.expand.go(0n, rest, as), {==}, pv.ex_plain(0n, rest, as))
            case Cv.CRun{n}:
              {==}
            case Cv.CGone{n}:
              {==}
    case 1n+(+e):
      match cs:
        case Nil{}:
          {==}
        case c <> +rest:
          match c:
            case Cv.CSet{i, v}:
              pv.plain_cat(Cv.Flat{[Cv.CSet{i, v}]}, Cv.expand.go(1n+e, rest, as), {==}, pv.ex_plain(1n+e, rest, as))
            case Cv.CToggle{i}:
              pv.plain_cat(Cv.Flat{[Cv.CToggle{i}]}, Cv.expand.go(1n+e, rest, as), {==}, pv.ex_plain(1n+e, rest, as))
            case Cv.CRun{+n}:
              pv.plain_cat(Cv.expand.go(e, Cv.body(as, n), as), Cv.expand.go(1n+e, rest, as), pv.ex_plain(e, Cv.body(as, n), as), pv.ex_plain(1n+e, rest, as))
            case Cv.CGone{n}:
              {==}

def pv.body_head(+n: Nat, +b: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> {Cv.body(Cv.Alias{n, b} <> as, n) == b : List<&2, Cv.Cmd>}:
  %pv.eq_refl(n) : {Cv.body.go(Cv.Alias{n, b} <> as, n, _) == b : List<&2, Cv.Cmd>}
  {==}

def pv.self(k: Nat, +n: Nat, +as: List<&2, Cv.Alias>) -> {Cv.expand.go(k, [Cv.CRun{n}], Cv.Alias{n, [Cv.CRun{n}]} <> as) == Cv.Cycle{} : Cv.Exp}:
  match k:
    case 0n:
      {==}
    case 1n+e:
      +t = {Cv.Alias{n, [Cv.CRun{n}]} <> as : List<&2, Cv.Alias>}
      %Equal.sym(List<&2, Cv.Cmd>, Cv.body(t, n), [Cv.CRun{n}], pv.body_head(n, [Cv.CRun{n}], as)) : {Cv.cat(Cv.expand.go(e, _, t), Cv.Flat{Nil{}}) == Cv.Cycle{} : Cv.Exp}
      %Equal.sym(Cv.Exp, Cv.expand.go(e, [Cv.CRun{n}], t), Cv.Cycle{}, pv.self(e, n, as)) : {Cv.cat(_, Cv.Flat{Nil{}}) == Cv.Cycle{} : Cv.Exp}
      {==}

def pv.gone(k: Nat, +n: Nat, +as: List<&2, Cv.Alias>) -> {Cv.cat(Cv.expand.go(k, [Cv.CGone{n}], as), Cv.Flat{Nil{}}) == Cv.Unknown{} : Cv.Exp}:
  match k:
    case 0n:
      {==}
    case 1n+e:
      {==}

# a plain list expands to itself at any depth
def pv.flat(b: List<&2, Cv.Cmd>, k: Nat, +as: List<&2, Cv.Alias>, h: {Cv.plain(b) == True{} : Bool}) -> {Cv.expand.go(k, b, as) == Cv.Flat{b} : Cv.Exp}:
  match b:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+e:
          {==}
    case c <> +rest:
      match c:
        case Cv.CSet{+i, +v}:
          match k:
            case 0n:
              %Equal.sym(Cv.Exp, Cv.expand.go(0n, rest, as), Cv.Flat{rest}, pv.flat(rest, 0n, as, h)) : {Cv.cat(Cv.Flat{[Cv.CSet{i, v}]}, _) == Cv.Flat{Cv.CSet{i, v} <> rest} : Cv.Exp}
              {==}
            case 1n+(+e):
              %Equal.sym(Cv.Exp, Cv.expand.go(1n+e, rest, as), Cv.Flat{rest}, pv.flat(rest, 1n+e, as, h)) : {Cv.cat(Cv.Flat{[Cv.CSet{i, v}]}, _) == Cv.Flat{Cv.CSet{i, v} <> rest} : Cv.Exp}
              {==}
        case Cv.CToggle{+i}:
          match k:
            case 0n:
              %Equal.sym(Cv.Exp, Cv.expand.go(0n, rest, as), Cv.Flat{rest}, pv.flat(rest, 0n, as, h)) : {Cv.cat(Cv.Flat{[Cv.CToggle{i}]}, _) == Cv.Flat{Cv.CToggle{i} <> rest} : Cv.Exp}
              {==}
            case 1n+(+e):
              %Equal.sym(Cv.Exp, Cv.expand.go(1n+e, rest, as), Cv.Flat{rest}, pv.flat(rest, 1n+e, as, h)) : {Cv.cat(Cv.Flat{[Cv.CToggle{i}]}, _) == Cv.Flat{Cv.CToggle{i} <> rest} : Cv.Exp}
              {==}
        case Cv.CRun{n}:
          pv.absurdF({Cv.expand.go(k, Cv.CRun{n} <> rest, as) == Cv.Flat{Cv.CRun{n} <> rest} : Cv.Exp}, h)
        case Cv.CGone{n}:
          pv.absurdF({Cv.expand.go(k, Cv.CGone{n} <> rest, as) == Cv.Flat{Cv.CGone{n} <> rest} : Cv.Exp}, h)

# The laws
# --------

def pv.cvar_registry_unique(xs: List<&2, Cv.Decl>) -> {Cv.unique(Cv.registry(xs)) == True{} : Bool}:
  pv.reg_unique(xs, Nil{}, {==})

def pv.cvar_registry_typed(xs: List<&2, Cv.Decl>) -> {Cv.all_typed(Cv.registry(xs)) == True{} : Bool}:
  pv.reg_typed(xs, Nil{}, {==})

def pv.cvar_value_typed(+xs: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.typed.at(Cv.find(Cv.registry(xs), x), Cv.value(Cv.registry(xs), cfg, fam, x)) == True{} : Bool}:
  pv.vt_m(Cv.find(Cv.registry(xs), x), Cv.registry(xs), cfg, fam, x, {==}, pv.cvar_registry_typed(xs))

def pv.cvar_inherits(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{Nil{}, Nil{}}]), x) == Cv.value(ds, cfg, fam, x) : Maybe<&2, Cv.Val>}:
  pv.inh_m(Cv.find(ds, x), ds, cfg, fam, x)

def pv.cvar_set_wins(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, +v: Cv.Val, ok: {Cv.valid(ds, Cv.Agent{}, Cv.Bind{x, v}) == True{} : Bool}) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, List.append(&2, Cv.Bind, ss, [Cv.Bind{x, v}])}]), x) == Some{v} : Maybe<&2, Cv.Val>}:
  pv.sw_m(Cv.find(ds, x), ds, cfg, fam, p, ss, x, v, {==}, ok)

def pv.cvar_global_uniform(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat, +d: Cv.Decl, found: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, global: {Cv.Decl.local(d) == False{} : Bool}) -> {Cv.value(ds, cfg, fam, x) == Some{Cv.root.val(ds, cfg, x, d)} : Maybe<&2, Cv.Val>}:
  pv.gu(ds, cfg, fam, x, d, found, global)

def pv.cvar_written_flagged(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag) -> {Cv.all_flag(Cv.written(ss, ds, f), ds, f) == True{} : Bool}:
  pv.wf_top(ss, ds, f)

def pv.cvar_persist_roundtrip(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, keeps: {Cv.flag.at(Cv.find(ds, x), Cv.Persist{}) == True{} : Bool}) -> {Cv.value(ds, cfg, [Cv.Ag{Cv.written(ss, ds, Cv.Persist{}), Nil{}}], x) == Cv.value(ds, cfg, [Cv.Ag{Nil{}, ss}], x) : Maybe<&2, Cv.Val>}:
  pv.pr_m(Cv.find(ds, x), ds, cfg, ss, x, keeps)

def pv.cvar_toggle_twice(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +a: Cv.Ag, +x: Nat) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.toggle(ds, cfg, fam, a, x), x)]), x) == Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) : Maybe<&2, Cv.Val>}:
  match a:
    case Cv.Ag{p, ss}:
      pv.tog_m(Cv.find(ds, x), ds, cfg, fam, p, ss, x, {==})

def pv.alias_expands_fully(cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> {Cv.Exp.plain(Cv.expand(cs, as)) == True{} : Bool}:
  pv.ex_plain(1n+List.length(&2, Cv.Alias, as), cs, as)

def pv.alias_self_cycle(+n: Nat, +as: List<&2, Cv.Alias>) -> {Cv.expand([Cv.CRun{n}], Cv.Alias{n, [Cv.CRun{n}]} <> as) == Cv.Cycle{} : Cv.Exp}:
  pv.self(1n+List.length(&2, Cv.Alias, Cv.Alias{n, [Cv.CRun{n}]} <> as), n, as)

def pv.alias_unknown_reported(+n: Nat, +as: List<&2, Cv.Alias>, gone: {Cv.body(as, n) == [Cv.CGone{n}] : List<&2, Cv.Cmd>}) -> {Cv.expand([Cv.CRun{n}], as) == Cv.Unknown{} : Cv.Exp}:
  %Equal.sym(List<&2, Cv.Cmd>, Cv.body(as, n), [Cv.CGone{n}], gone) : {Cv.cat(Cv.expand.go(List.length(&2, Cv.Alias, as), _, as), Cv.Flat{Nil{}}) == Cv.Unknown{} : Cv.Exp}
  pv.gone(List.length(&2, Cv.Alias, as), n, as)

def pv.alias_runs_body(+n: Nat, +b: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, flat: {Cv.plain(b) == True{} : Bool}) -> {Cv.expand([Cv.CRun{n}], Cv.Alias{n, b} <> as) == Cv.Flat{b} : Cv.Exp}:
  +t = {Cv.Alias{n, b} <> as : List<&2, Cv.Alias>}
  +k = List.length(&2, Cv.Alias, t)
  %Equal.sym(List<&2, Cv.Cmd>, Cv.body(t, n), b, pv.body_head(n, b, as)) : {Cv.cat(Cv.expand.go(k, _, t), Cv.Flat{Nil{}}) == Cv.Flat{b} : Cv.Exp}
  %Equal.sym(Cv.Exp, Cv.expand.go(k, b, t), Cv.Flat{b}, pv.flat(b, k, t, flat)) : {Cv.cat(_, Cv.Flat{Nil{}}) == Cv.Flat{b} : Cv.Exp}
  Equal.cong(List<&2, Cv.Cmd>, Cv.Exp, z => Cv.Flat{z}, List.append(&2, Cv.Cmd, b, Nil{}), b, pv.app_nil(b))

def pv.bind_press_plain(+bs: List<&2, Cv.KeyBind>, +k: Nat, +as: List<&2, Cv.Alias>) -> {Cv.Exp.plain(Cv.press(bs, k, as)) == True{} : Bool}:
  pv.ex_plain(1n+List.length(&2, Cv.Alias, as), Cv.bound(bs, k), as)

def pv.bind_unbound_runs_nothing(+bs: List<&2, Cv.KeyBind>, +k: Nat, +as: List<&2, Cv.Alias>, free: {Cv.bound(bs, k) == Nil{} : List<&2, Cv.Cmd>}) -> {Cv.press(bs, k, as) == Cv.Flat{Nil{}} : Cv.Exp}:
  %Equal.sym(List<&2, Cv.Cmd>, Cv.bound(bs, k), Nil{}, free) : {Cv.expand(_, as) == Cv.Flat{Nil{}} : Cv.Exp}
  {==}

def pv.bind_first_wins(+k: Nat, +c: List<&2, Cv.Cmd>, +rest: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>) -> {Cv.press(Cv.KeyBind{k, c} <> rest, k, as) == Cv.expand(c, as) : Cv.Exp}:
  %pv.eq_refl(k) : {Cv.expand(Cv.bound.go(Cv.KeyBind{k, c} <> rest, k, _), as) == Cv.expand(c, as) : Cv.Exp}
  {==}

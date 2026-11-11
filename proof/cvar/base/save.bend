# eukhe: lemmas of area cvar on the stores of the config layer (Cv.drop,
# Cv.save, Cv.stores): a layer over two lists in a row, a layer on any
# current value, a set that hits its cvar and misses every other one, a
# layer of a cvar read from that cvar's sets alone.

import Base
import ../../../bend/cvar.bend as Cv
import ../../../laws/cvar/resolution.bend as Cvar
import ../base.bend as LA

# Layers on a current value
# -------------------------

# the value m, else cur
def sv.orm(m: Maybe<&2, Cv.Val>, cur: Maybe<&2, Cv.Val>) -> Maybe<&2, Cv.Val>:
  match m:
    case None{}:
      cur
    case Some{a}:
      Some{a}

def sv.orm_assoc(a: Maybe<&2, Cv.Val>, +b: Maybe<&2, Cv.Val>, +c: Maybe<&2, Cv.Val>) -> {sv.orm(a, sv.orm(b, c)) == sv.orm(sv.orm(a, b), c) : Maybe<&2, Cv.Val>}:
  match a:
    case None{}:
      {==}
    case Some{y}:
      {==}

def sv.one_go(b: Bool, +s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer.go([s], ds, l, x, cur, b) == sv.orm(Cv.layer.go([s], ds, l, x, None{}, b), cur) : Maybe<&2, Cv.Val>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# one set on cur: its value when it hits, else cur
def sv.one(+s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer([s], ds, l, x, cur) == sv.orm(Cv.layer([s], ds, l, x, None{}), cur) : Maybe<&2, Cv.Val>}:
  sv.one_go(Cv.hit.at([s], ds, l, x), s, ds, l, x, cur)

# a layer on cur is its value on None, else cur: a layer with no hit
# keeps any cur, one with a hit answers its value from any cur
def sv.or(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer(ss, ds, l, x, cur) == sv.orm(Cv.layer(ss, ds, l, x, None{}), cur) : Maybe<&2, Cv.Val>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +r:
      +c1 = Cv.layer([s], ds, l, x, cur)
      +n1 = Cv.layer([s], ds, l, x, None{})
      +nr = Cv.layer(r, ds, l, x, None{})
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> r, ds, l, x, cur), Cv.layer(r, ds, l, x, c1), LA.pv.layer_cons(s, r, ds, l, x, cur)) : {_ == sv.orm(Cv.layer(s <> r, ds, l, x, None{}), cur) : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> r, ds, l, x, None{}), Cv.layer(r, ds, l, x, n1), LA.pv.layer_cons(s, r, ds, l, x, None{})) : {Cv.layer(r, ds, l, x, c1) == sv.orm(_, cur) : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(r, ds, l, x, n1), sv.orm(nr, n1), sv.or(r, ds, l, x, n1)) : {Cv.layer(r, ds, l, x, c1) == sv.orm(_, cur) : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(r, ds, l, x, c1), sv.orm(nr, c1), sv.or(r, ds, l, x, c1)) : {_ == sv.orm(sv.orm(nr, n1), cur) : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, c1, sv.orm(n1, cur), sv.one(s, ds, l, x, cur)) : {sv.orm(nr, _) == sv.orm(sv.orm(nr, n1), cur) : Maybe<&2, Cv.Val>}
      sv.orm_assoc(nr, n1, cur)

# a layer over a then b is b's layer on a's
def sv.app(a: List<&2, Cv.Bind>, +b: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer(List.append(&2, Cv.Bind, a, b), ds, l, x, cur) == Cv.layer(b, ds, l, x, Cv.layer(a, ds, l, x, cur)) : Maybe<&2, Cv.Val>}:
  match a:
    case Nil{}:
      {==}
    case +s <> +r:
      +c1 = Cv.layer([s], ds, l, x, cur)
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> List.append(&2, Cv.Bind, r, b), ds, l, x, cur), Cv.layer(List.append(&2, Cv.Bind, r, b), ds, l, x, c1), LA.pv.layer_cons(s, List.append(&2, Cv.Bind, r, b), ds, l, x, cur)) : {_ == Cv.layer(b, ds, l, x, Cv.layer(s <> r, ds, l, x, cur)) : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> r, ds, l, x, cur), Cv.layer(r, ds, l, x, c1), LA.pv.layer_cons(s, r, ds, l, x, cur)) : {Cv.layer(List.append(&2, Cv.Bind, r, b), ds, l, x, c1) == Cv.layer(b, ds, l, x, _) : Maybe<&2, Cv.Val>}
      sv.app(r, b, ds, l, x, c1)

# Hits and misses of a write
# --------------------------

# the set of x to v hits x when it is valid
def sv.hit_self(+ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +v: Cv.Val, ok: {Cv.valid(ds, l, Cv.Bind{x, v}) == True{} : Bool}) -> {Cv.hit.at([Cv.Bind{x, v}], ds, l, x) == True{} : Bool}:
  %LA.cvar.pv.eq_refl(x) : {Cv.hit.when(_, ds, l, Cv.Bind{x, v}) == True{} : Bool}
  ok

# a set of x misses every other cvar y
def sv.miss_other(+ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +v: Cv.Val, +y: Nat, ne: {Nat.is_eq(x, y) == False{} : Bool}) -> {Cv.hit.at([Cv.Bind{x, v}], ds, l, y) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(x, y), False{}, ne) : {Cv.hit.when(_, ds, l, Cv.Bind{x, v}) == False{} : Bool}
  {==}

# A layer reads a cvar from its sets alone
# ----------------------------------------

def sv.only_at(h: Bool, +i: Nat, +w: Cv.Val, +r: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>, eh: {Nat.is_eq(i, x) == h : Bool}, ih: @c: Maybe<&2, Cv.Val> -> {Cv.layer(r, ds, l, x, c) == Cv.layer(Cvar.spec_sets_of(r, x), ds, l, x, c) : Maybe<&2, Cv.Val>}) -> {Cv.layer(Cv.Bind{i, w} <> r, ds, l, x, cur) == Cv.layer(Cvar.spec_sets_of.pick(h, Cv.Bind{i, w}, Cvar.spec_sets_of(r, x)), ds, l, x, cur) : Maybe<&2, Cv.Val>}:
  match h:
    case True{}:
      +s = {Cv.Bind{i, w} : Cv.Bind}
      +sr = Cvar.spec_sets_of(r, x)
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> r, ds, l, x, cur), Cv.layer(r, ds, l, x, Cv.layer([s], ds, l, x, cur)), LA.pv.layer_cons(s, r, ds, l, x, cur)) : {_ == Cv.layer(s <> sr, ds, l, x, cur) : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> sr, ds, l, x, cur), Cv.layer(sr, ds, l, x, Cv.layer([s], ds, l, x, cur)), LA.pv.layer_cons(s, sr, ds, l, x, cur)) : {Cv.layer(r, ds, l, x, Cv.layer([s], ds, l, x, cur)) == _ : Maybe<&2, Cv.Val>}
      ih(Cv.layer([s], ds, l, x, cur))
    case False{}:
      +s = {Cv.Bind{i, w} : Cv.Bind}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> r, ds, l, x, cur), Cv.layer(r, ds, l, x, Cv.layer([s], ds, l, x, cur)), LA.pv.layer_cons(s, r, ds, l, x, cur)) : {_ == Cv.layer(Cvar.spec_sets_of(r, x), ds, l, x, cur) : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer([s], ds, l, x, cur), cur, LA.pv.layer_miss(s, ds, l, x, cur, sv.miss_other(ds, l, i, w, x, eh))) : {Cv.layer(r, ds, l, x, _) == Cv.layer(Cvar.spec_sets_of(r, x), ds, l, x, cur) : Maybe<&2, Cv.Val>}
      ih(cur)

# the layer of x over ss is the layer over the sets of x in ss
def sv.only(g: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer(g, ds, l, x, cur) == Cv.layer(Cvar.spec_sets_of(g, x), ds, l, x, cur) : Maybe<&2, Cv.Val>}:
  match g:
    case Nil{}:
      {==}
    case Cv.Bind{+i, +w} <> +r:
      sv.only_at(Nat.is_eq(i, x), i, w, r, ds, l, x, cur, {==}, c => sv.only(r, ds, l, x, c))

# The stores
# ----------

# the config layer of the stores, read with no family: the project's
# layer on the global config.cfg's on settings.json's
def sv.stores(+ds: List<&2, Cv.Decl>, +doc: List<&2, Cv.Bind>, +g: List<&2, Cv.Bind>, +p: List<&2, Cv.Bind>, +x: Nat) -> {Cv.layered(ds, Cv.stores(doc, g, p), Nil{}, x) == Cv.layer(p, ds, Cv.Config{}, x, Cv.layer(g, ds, Cv.Config{}, x, Cv.layer(doc, ds, Cv.Config{}, x, None{}))) : Maybe<&2, Cv.Val>}:
  +c0 = Cv.layer(doc, ds, Cv.Config{}, x, None{})
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, doc, List.append(&2, Cv.Bind, g, p)), ds, Cv.Config{}, x, None{}), Cv.layer(List.append(&2, Cv.Bind, g, p), ds, Cv.Config{}, x, c0), sv.app(doc, List.append(&2, Cv.Bind, g, p), ds, Cv.Config{}, x, None{})) : {_ == Cv.layer(p, ds, Cv.Config{}, x, Cv.layer(g, ds, Cv.Config{}, x, c0)) : Maybe<&2, Cv.Val>}
  sv.app(g, p, ds, Cv.Config{}, x, c0)

# Sets of a cvar
# --------------

def sv.sets_pick(h: Bool, +s: Cv.Bind, +a: List<&2, Cv.Bind>, +b: List<&2, Cv.Bind>, +c: List<&2, Cv.Bind>, ih: {a == List.append(&2, Cv.Bind, b, c) : List<&2, Cv.Bind>}) -> {Cvar.spec_sets_of.pick(h, s, a) == List.append(&2, Cv.Bind, Cvar.spec_sets_of.pick(h, s, b), c) : List<&2, Cv.Bind>}:
  match h:
    case True{}:
      %Equal.sym(List<&2, Cv.Bind>, a, List.append(&2, Cv.Bind, b, c), ih) : {s <> _ == s <> List.append(&2, Cv.Bind, b, c) : List<&2, Cv.Bind>}
      {==}
    case False{}:
      ih

# the sets of x in a then b
def sv.sets_app(a: List<&2, Cv.Bind>, +b: List<&2, Cv.Bind>, +x: Nat) -> {Cvar.spec_sets_of(List.append(&2, Cv.Bind, a, b), x) == List.append(&2, Cv.Bind, Cvar.spec_sets_of(a, x), Cvar.spec_sets_of(b, x)) : List<&2, Cv.Bind>}:
  match a:
    case Nil{}:
      {==}
    case Cv.Bind{+i, +w} <> +r:
      sv.sets_pick(Nat.is_eq(i, x), Cv.Bind{i, w}, Cvar.spec_sets_of(List.append(&2, Cv.Bind, r, b), x), Cvar.spec_sets_of(r, x), Cvar.spec_sets_of(b, x), sv.sets_app(r, b, x))

def sv.sets_drop_at(h: Bool, +i: Nat, +w: Cv.Val, +x: Nat, +d: List<&2, Cv.Bind>, eh: {Nat.is_eq(i, x) == h : Bool}, ih: {Cvar.spec_sets_of(d, x) == Nil{} : List<&2, Cv.Bind>}) -> {Cvar.spec_sets_of(Cv.drop.at(h, Cv.Bind{i, w}, d), x) == Nil{} : List<&2, Cv.Bind>}:
  match h:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), False{}, eh) : {Cvar.spec_sets_of.pick(_, Cv.Bind{i, w}, Cvar.spec_sets_of(d, x)) == Nil{} : List<&2, Cv.Bind>}
      ih

# no set of x is left after its sets are dropped
def sv.sets_drop(g: List<&2, Cv.Bind>, +x: Nat) -> {Cvar.spec_sets_of(Cv.drop(g, x), x) == Nil{} : List<&2, Cv.Bind>}:
  match g:
    case Nil{}:
      {==}
    case Cv.Bind{+i, +w} <> +r:
      sv.sets_drop_at(Nat.is_eq(i, x), i, w, x, Cv.drop(r, x), {==}, sv.sets_drop(r, x))

# a set whose id is x misses every other cvar y
def sv.miss_id(+s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +y: Nat, eb: {Nat.is_eq(Cv.Bind.id(s), x) == True{} : Bool}, ne: {Nat.is_eq(x, y) == False{} : Bool}) -> {Cv.hit.at([s], ds, l, y) == False{} : Bool}:
  %Equal.sym(Nat, Cv.Bind.id(s), x, LA.pv.eq_true(Cv.Bind.id(s), x, eb)) : {Cv.hit.when(Nat.is_eq(_, y), ds, l, s) == False{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(x, y), False{}, ne) : {Cv.hit.when(_, ds, l, s) == False{} : Bool}
  {==}

def sv.drop_step(b: Bool, +s: Cv.Bind, +r: List<&2, Cv.Bind>, +x: Nat, +y: Nat, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +cur: Maybe<&2, Cv.Val>, eb: {Nat.is_eq(Cv.Bind.id(s), x) == b : Bool}, ne: {Nat.is_eq(x, y) == False{} : Bool},
  ih0: {Cv.layer(Cv.drop(r, x), ds, l, y, cur) == Cv.layer(r, ds, l, y, cur) : Maybe<&2, Cv.Val>},
  ih1: {Cv.layer(Cv.drop(r, x), ds, l, y, Cv.layer([s], ds, l, y, cur)) == Cv.layer(r, ds, l, y, Cv.layer([s], ds, l, y, cur)) : Maybe<&2, Cv.Val>})
  -> {Cv.layer(Cv.drop.at(b, s, Cv.drop(r, x)), ds, l, y, cur) == Cv.layer(s <> r, ds, l, y, cur) : Maybe<&2, Cv.Val>}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> r, ds, l, y, cur), Cv.layer(r, ds, l, y, Cv.layer([s], ds, l, y, cur)), LA.pv.layer_cons(s, r, ds, l, y, cur)) : {Cv.layer(Cv.drop(r, x), ds, l, y, cur) == _ : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer([s], ds, l, y, cur), cur, LA.pv.layer_miss(s, ds, l, y, cur, sv.miss_id(s, ds, l, x, y, eb, ne))) : {Cv.layer(Cv.drop(r, x), ds, l, y, cur) == Cv.layer(r, ds, l, y, _) : Maybe<&2, Cv.Val>}
      ih0
    case False{}:
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> Cv.drop(r, x), ds, l, y, cur), Cv.layer(Cv.drop(r, x), ds, l, y, Cv.layer([s], ds, l, y, cur)), LA.pv.layer_cons(s, Cv.drop(r, x), ds, l, y, cur)) : {_ == Cv.layer(s <> r, ds, l, y, cur) : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> r, ds, l, y, cur), Cv.layer(r, ds, l, y, Cv.layer([s], ds, l, y, cur)), LA.pv.layer_cons(s, r, ds, l, y, cur)) : {Cv.layer(Cv.drop(r, x), ds, l, y, Cv.layer([s], ds, l, y, cur)) == _ : Maybe<&2, Cv.Val>}
      ih1

# dropping the sets of x keeps the layer of every other cvar y
def sv.drop_keeps(g: List<&2, Cv.Bind>, +x: Nat, +y: Nat, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +cur: Maybe<&2, Cv.Val>, +ne: {Nat.is_eq(x, y) == False{} : Bool}) -> {Cv.layer(Cv.drop(g, x), ds, l, y, cur) == Cv.layer(g, ds, l, y, cur) : Maybe<&2, Cv.Val>}:
  match g:
    case Nil{}:
      {==}
    case +s <> +r:
      sv.drop_step(Nat.is_eq(Cv.Bind.id(s), x), s, r, x, y, ds, l, cur, {==}, ne, sv.drop_keeps(r, x, y, ds, l, cur, ne), sv.drop_keeps(r, x, y, ds, l, Cv.layer([s], ds, l, y, cur), ne))

# a write of x leaves the store's layer of every other cvar y
def sv.save_keeps(+g: List<&2, Cv.Bind>, +x: Nat, +v: Cv.Val, +y: Nat, +ds: List<&2, Cv.Decl>, +cur: Maybe<&2, Cv.Val>, +ne: {Nat.is_eq(x, y) == False{} : Bool}) -> {Cv.layer(Cv.save(g, Cv.Bind{x, v}), ds, Cv.Config{}, y, cur) == Cv.layer(g, ds, Cv.Config{}, y, cur) : Maybe<&2, Cv.Val>}:
  +b = {Cv.Bind{x, v} : Cv.Bind}
  +d = Cv.drop(g, x)
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(Cv.save(g, b), ds, Cv.Config{}, y, cur), Cv.layer([b], ds, Cv.Config{}, y, Cv.layer(d, ds, Cv.Config{}, y, cur)), LA.pv.layer_snoc(d, b, ds, Cv.Config{}, y, cur)) : {_ == Cv.layer(g, ds, Cv.Config{}, y, cur) : Maybe<&2, Cv.Val>}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer([b], ds, Cv.Config{}, y, Cv.layer(d, ds, Cv.Config{}, y, cur)), Cv.layer(d, ds, Cv.Config{}, y, cur), LA.pv.layer_miss(b, ds, Cv.Config{}, y, Cv.layer(d, ds, Cv.Config{}, y, cur), sv.miss_other(ds, Cv.Config{}, x, v, y, ne))) : {_ == Cv.layer(g, ds, Cv.Config{}, y, cur) : Maybe<&2, Cv.Val>}
  sv.drop_keeps(g, x, y, ds, Cv.Config{}, cur, ne)

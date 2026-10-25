# eukhe: the proof of LAW cvar_toggle_twice

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base.bend as LA

def pv.not_not(b: Bool) -> {Bool.not(Bool.not(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Toggle
# ------

def pv.G_some(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +a: Cv.Ag, +x: Nat, +d: Cv.Decl, em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) == Some{Cv.over(ds, a, x, Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d)))} : Maybe<&2, Cv.Val>}:
  +r = Cv.root.val(ds, cfg, x, d)
  %Equal.sym(Maybe<&2, Cv.Decl>, Cv.find(ds, x), Some{d}, em) : {Cv.value.at(_, ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) == Some{Cv.over(ds, a, x, Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d)))} : Maybe<&2, Cv.Val>}
  Equal.cong(Cv.Val, Maybe<&2, Cv.Val>, y => Some{y}, Cv.chain(List.append(&2, Cv.Ag, fam, [a]), ds, x, r), Cv.over(ds, a, x, Cv.chain(fam, ds, x, r)), LA.pv.chain_snoc(fam, a, ds, x, r))

def pv.T_eq(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +a: Cv.Ag, +x: Nat, +d: Cv.Decl, em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, +y: Cv.Val, ey: {Cv.over(ds, a, x, Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d))) == y : Cv.Val}) -> {Cv.toggle(ds, cfg, fam, a, x) == Cv.add(a, Cv.flip(x, Some{y})) : Cv.Ag}:
  +o = Cv.over(ds, a, x, Cv.chain(fam, ds, x, Cv.root.val(ds, cfg, x, d)))
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x), Some{o}, pv.G_some(ds, cfg, fam, a, x, d, em)) : {Cv.add(a, Cv.flip(x, _)) == Cv.add(a, Cv.flip(x, Some{y})) : Cv.Ag}
  %Equal.sym(Cv.Val, o, y, ey) : {Cv.add(a, Cv.flip(x, Some{_})) == Cv.add(a, Cv.flip(x, Some{y})) : Cv.Ag}
  {==}

def pv.O_snoc_miss(+ds: List<&2, Cv.Decl>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +s: Cv.Bind, +x: Nat, +r: Cv.Val, h: {Cv.hit.at([s], ds, Cv.Agent{}, x) == False{} : Bool}) -> {Cv.over(ds, Cv.Ag{p, List.append(&2, Cv.Bind, ss, [s])}, x, r) == Cv.over(ds, Cv.Ag{p, ss}, x, r) : Cv.Val}:
  +q = Cv.layer(p, ds, Cv.Agent{}, x, None{})
  +c = Cv.layer(ss, ds, Cv.Agent{}, x, q)
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, ss, [s]), ds, Cv.Agent{}, x, q), Cv.layer([s], ds, Cv.Agent{}, x, c), LA.pv.layer_snoc(ss, s, ds, Cv.Agent{}, x, q)) : {Maybe.default(&2, Cv.Val, _, r) == Cv.over(ds, Cv.Ag{p, ss}, x, r) : Cv.Val}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer([s], ds, Cv.Agent{}, x, c), c, LA.pv.layer_miss(s, ds, Cv.Agent{}, x, c, h)) : {Maybe.default(&2, Cv.Val, _, r) == Cv.over(ds, Cv.Ag{p, ss}, x, r) : Cv.Val}
  {==}

def pv.O_snoc_hit(+ds: List<&2, Cv.Decl>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +s: Cv.Bind, +x: Nat, +r: Cv.Val, h: {Cv.hit.at([s], ds, Cv.Agent{}, x) == True{} : Bool}) -> {Cv.over(ds, Cv.Ag{p, List.append(&2, Cv.Bind, ss, [s])}, x, r) == Cv.Bind.val(s) : Cv.Val}:
  +q = Cv.layer(p, ds, Cv.Agent{}, x, None{})
  +c = Cv.layer(ss, ds, Cv.Agent{}, x, q)
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, ss, [s]), ds, Cv.Agent{}, x, q), Cv.layer([s], ds, Cv.Agent{}, x, c), LA.pv.layer_snoc(ss, s, ds, Cv.Agent{}, x, q)) : {Maybe.default(&2, Cv.Val, _, r) == Cv.Bind.val(s) : Cv.Val}
  %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer([s], ds, Cv.Agent{}, x, c), Some{Cv.Bind.val(s)}, LA.pv.layer_hit(s, ds, Cv.Agent{}, x, c, h)) : {Maybe.default(&2, Cv.Val, _, r) == Cv.Bind.val(s) : Cv.Val}
  {==}

# a Bool set of x is valid whatever its Bool
def pv.vb_at(m: Maybe<&2, Cv.Decl>, +x: Nat, +c1: Bool, +c2: Bool) -> {Cv.valid.at(m, Cv.Agent{}, Cv.Bind{x, Cv.VBool{c1}}) == Cv.valid.at(m, Cv.Agent{}, Cv.Bind{x, Cv.VBool{c2}}) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      {==}

def pv.vb_hit(+ds: List<&2, Cv.Decl>, +x: Nat, +c1: Bool, +c2: Bool) -> {Cv.hit.at([Cv.Bind{x, Cv.VBool{c1}}], ds, Cv.Agent{}, x) == Cv.hit.at([Cv.Bind{x, Cv.VBool{c2}}], ds, Cv.Agent{}, x) : Bool}:
  %LA.cvar.pv.eq_refl(x) : {Cv.hit.when(_, ds, Cv.Agent{}, Cv.Bind{x, Cv.VBool{c1}}) == Cv.hit.when(_, ds, Cv.Agent{}, Cv.Bind{x, Cv.VBool{c2}}) : Bool}
  pv.vb_at(Cv.find(ds, x), x, c1, c2)

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

def pv.cvar_toggle_twice(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +a: Cv.Ag, +x: Nat) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.toggle(ds, cfg, fam, Cv.toggle(ds, cfg, fam, a, x), x)]), x) == Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [a]), x) : Maybe<&2, Cv.Val>}:
  match a:
    case Cv.Ag{p, ss}:
      pv.tog_m(Cv.find(ds, x), ds, cfg, fam, p, ss, x, {==})

def Cvar.cvar_toggle_twice(ds, cfg, fam, a, x):
  pv.cvar_toggle_twice(ds, cfg, fam, a, x)

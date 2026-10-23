# eukhe: the proof of LAW cvar_global_uniform

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base.bend as LA

# Global cvars
# ------------

def pv.global_miss(b: Bool, +s: Cv.Bind, +ds: List<&2, Cv.Decl>, +x: Nat, +d: Cv.Decl, eb: {Nat.is_eq(Cv.Bind.id(s), x) == b : Bool}, em: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, gl: {Cv.Decl.local(d) == False{} : Bool}) -> {Bool.and(b, Cv.valid(ds, Cv.Agent{}, s)) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, Cv.Bind.id(s), x, LA.pv.eq_true(Cv.Bind.id(s), x, eb)) : {Cv.valid.at(Cv.find(ds, _), Cv.Agent{}, s) == False{} : Bool}
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
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(s <> r, ds, Cv.Agent{}, x, cur), Cv.layer(r, ds, Cv.Agent{}, x, c1), LA.pv.layer_cons(s, r, ds, Cv.Agent{}, x, cur)) : {_ == cur : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, c1, cur, LA.pv.layer_miss(s, ds, Cv.Agent{}, x, cur, miss)) : {Cv.layer(r, ds, Cv.Agent{}, x, _) == cur : Maybe<&2, Cv.Val>}
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

def pv.cvar_global_uniform(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +x: Nat, +d: Cv.Decl, found: {Cv.find(ds, x) == Some{d} : Maybe<&2, Cv.Decl>}, global: {Cv.Decl.local(d) == False{} : Bool}) -> {Cv.value(ds, cfg, fam, x) == Some{Cv.root.val(ds, cfg, x, d)} : Maybe<&2, Cv.Val>}:
  pv.gu(ds, cfg, fam, x, d, found, global)

def Cvar.cvar_global_uniform(ds, cfg, fam, x, d, found, global):
  pv.cvar_global_uniform(ds, cfg, fam, x, d, found, global)

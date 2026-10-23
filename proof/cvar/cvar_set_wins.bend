# eukhe: the proof of LAW cvar_set_wins

import Base
import ../../bend/cvar.bend as Cv
import ../../LAWS.bend as Laws
import ./base.bend as LA

# the set of x to v hits x when it is valid
def pv.hit_self(+ds: List<&2, Cv.Decl>, +x: Nat, +v: Cv.Val, ok: {Cv.valid(ds, Cv.Agent{}, Cv.Bind{x, v}) == True{} : Bool}) -> {Cv.hit.at([Cv.Bind{x, v}], ds, Cv.Agent{}, x) == True{} : Bool}:
  %LA.cvar.pv.eq_refl(x) : {Bool.and(_, Cv.valid(ds, Cv.Agent{}, Cv.Bind{x, v})) == True{} : Bool}
  ok

def pv.sw_m(m: Maybe<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, +v: Cv.Val, em: {Cv.find(ds, x) == m : Maybe<&2, Cv.Decl>}, +ok: {Cv.valid(ds, Cv.Agent{}, Cv.Bind{x, v}) == True{} : Bool}) -> {Cv.value.at(m, ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, List.append(&2, Cv.Bind, ss, [Cv.Bind{x, v}])}]), x) == Some{v} : Maybe<&2, Cv.Val>}:
  match m:
    case None{}:
      LA.pv.absurdF({None{} == Some{v} : Maybe<&2, Cv.Val>}, LA.pv.valid_m(ds, Cv.Agent{}, Cv.Bind{x, v}, x, None{}, em, {==}, ok))
    case Some{+d}:
      +r = Cv.root.val(ds, cfg, x, d)
      +ag = {Cv.Ag{p, List.append(&2, Cv.Bind, ss, [Cv.Bind{x, v}])} : Cv.Ag}
      +c = Cv.chain(fam, ds, x, r)
      +lp = Cv.layer(p, ds, Cv.Agent{}, x, None{})
      +q = Cv.layer(ss, ds, Cv.Agent{}, x, lp)
      %Equal.sym(Cv.Val, Cv.chain(List.append(&2, Cv.Ag, fam, [ag]), ds, x, r), Cv.over(ds, ag, x, c), LA.pv.chain_snoc(fam, ag, ds, x, r)) : {Some{_} == Some{v} : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(List.append(&2, Cv.Bind, ss, [Cv.Bind{x, v}]), ds, Cv.Agent{}, x, lp), Cv.layer([Cv.Bind{x, v}], ds, Cv.Agent{}, x, q), LA.pv.layer_snoc(ss, Cv.Bind{x, v}, ds, Cv.Agent{}, x, lp)) : {Some{Maybe.default(&2, Cv.Val, _, c)} == Some{v} : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer([Cv.Bind{x, v}], ds, Cv.Agent{}, x, q), Some{v}, LA.pv.layer_hit(Cv.Bind{x, v}, ds, Cv.Agent{}, x, q, pv.hit_self(ds, x, v, ok))) : {Some{Maybe.default(&2, Cv.Val, _, c)} == Some{v} : Maybe<&2, Cv.Val>}
      {==}

def pv.cvar_set_wins(+ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +p: List<&2, Cv.Bind>, +ss: List<&2, Cv.Bind>, +x: Nat, +v: Cv.Val, ok: {Cv.valid(ds, Cv.Agent{}, Cv.Bind{x, v}) == True{} : Bool}) -> {Cv.value(ds, cfg, List.append(&2, Cv.Ag, fam, [Cv.Ag{p, List.append(&2, Cv.Bind, ss, [Cv.Bind{x, v}])}]), x) == Some{v} : Maybe<&2, Cv.Val>}:
  pv.sw_m(Cv.find(ds, x), ds, cfg, fam, p, ss, x, v, {==}, ok)

def Laws.cvar_set_wins(ds, cfg, fam, p, ss, x, v, ok):
  pv.cvar_set_wins(ds, cfg, fam, p, ss, x, v, ok)

# eukhe: the proof of LAW env_merge_named_from_overlay

import Base
import ../../bend/child_env.bend as Env
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pce.not_both(-G: Type, -base: List<&2, Env.Var>, +over: List<&2, Env.Var>, +v: Env.Var, p: (Env.In(v, base) & {Env.named(Env.Var.name(v), over) == False{} : Bool}), hit: {Env.named(Env.Var.name(v), over) == True{} : Bool}) -> G:
  (a, f) = p
  LA.pce.absurd(G, Equal.trans(Bool, True{}, Env.named(Env.Var.name(v), over), False{}, Equal.sym(Bool, Env.named(Env.Var.name(v), over), True{}, hit), f))

def pce.over_of(+base: List<&2, Env.Var>, +over: List<&2, Env.Var>, +v: Env.Var, o: Or(Env.In(v, over), Env.In(v, Env.under(base, over))), hit: {Env.named(Env.Var.name(v), over) == True{} : Bool}) -> Env.In(v, over):
  match o:
    case Inl{a}:
      a
    case Inr{b}:
      pce.not_both(Env.In(v, over), base, over, v, LA.pce.under_out(base, over, v, b), hit)

def Laws.env_merge_named_from_overlay(base, over, v, i, hit):
  +n = Env.Var.name(v)
  pce.over_of(base, over, v, LA.pce.app_in(over, Env.under(base, over), v, i), Equal.trans(Bool, Env.named(n, over), Laws.env_named(n, over), True{}, Equal.sym(Bool, Laws.env_named(n, over), Env.named(n, over), LA.pce.named_eq(n, over)), hit))

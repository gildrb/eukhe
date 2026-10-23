# eukhe: the proof of LAW env_merge_from_inputs

import Base
import ../../bend/child_env.bend as Env
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pce.spec_free(-base: List<&2, Env.Var>, +over: List<&2, Env.Var>, +v: Env.Var, p: (Env.In(v, base) & {Env.named(Env.Var.name(v), over) == False{} : Bool})) -> (Env.In(v, base) & {Laws.env_named(Env.Var.name(v), over) == False{} : Bool}):
  (a, f) = p
  (a, Equal.trans(Bool, Laws.env_named(Env.Var.name(v), over), Env.named(Env.Var.name(v), over), False{}, LA.pce.named_eq(Env.Var.name(v), over), f))

def pce.from_inputs(+base: List<&2, Env.Var>, +over: List<&2, Env.Var>, +v: Env.Var, o: Or(Env.In(v, over), Env.In(v, Env.under(base, over)))) -> Or(Env.In(v, over), (Env.In(v, base) & {Laws.env_named(Env.Var.name(v), over) == False{} : Bool})):
  match o:
    case Inl{a}:
      Inl{a}
    case Inr{b}:
      Inr{pce.spec_free(base, over, v, LA.pce.under_out(base, over, v, b))}

def Laws.env_merge_from_inputs(base, over, v, i):
  pce.from_inputs(base, over, v, LA.pce.app_in(over, Env.under(base, over), v, i))

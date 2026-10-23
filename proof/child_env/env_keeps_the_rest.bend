# eukhe: the proof of LAW env_keeps_the_rest

import Base
import ../../bend/child_env.bend as Env
import ../../laws/child_env.bend as ChildEnv
import ./base.bend as LA

# a name that is not a credential passes
def pce.rest(c: Bool, +x: Bool, e: {c == False{} : Bool}) -> {Bool.or(Bool.not(c), x) == True{} : Bool}:
  match c:
    case True{}:
      LA.pce.absurd({Bool.or(False{}, x) == True{} : Bool}, e)
    case False{}:
      {==}

def pce.env_keeps_the_rest(+reg: List<&2, String>, +keep: List<&2, String>, base: List<&2, Env.Var>, over: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.merge(base, over)), c: {Env.cred(reg, Env.Var.name(v)) == False{} : Bool}) -> Env.In(v, Env.child(reg, keep, base, over)):
  +n = Env.Var.name(v)
  LA.pce.in_keep(reg, keep, Env.merge(base, over), v, i, LA.pce.of_spec(reg, keep, n, pce.rest(Env.cred(reg, n), Bool.and(Env.listed(keep, n), Bool.not(Env.registered(reg, n))), c)))

def ChildEnv.env_keeps_the_rest(reg, keep, base, over, v, i, c):
  pce.env_keeps_the_rest(reg, keep, base, over, v, i, c)

# eukhe: the proof of LAW env_drops_credentials

import Base
import ../../bend/child_env.bend as Env
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pce.or_false(a: Bool, h: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LA.pce.absurdF({False{} == True{} : Bool}, h)

# The laws
# --------

def pce.env_drops_credentials(+reg: List<&2, String>, base: List<&2, Env.Var>, over: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.child(reg, Nil{}, base, over))) -> {Env.cred(reg, Env.Var.name(v)) == False{} : Bool}:
  +n = Env.Var.name(v)
  LA.pce.not_t(Env.cred(reg, n), pce.or_false(Bool.not(Env.cred(reg, n)), LA.pce.spec_of(reg, Nil{}, n, LA.pce.child_passes(reg, Nil{}, Env.merge(base, over), v, i))))

# (G3) No credential reaches a child

def Laws.env_drops_credentials(reg, base, over, v, i):
  pce.env_drops_credentials(reg, base, over, v, i)

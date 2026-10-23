# eukhe: the proof of LAW env_keeps_listed

import Base
import ../../bend/child_env.bend as Env
import ../../LAWS.bend as Laws
import ./base.bend as LA

# a kept name that is no provider name passes
def pce.kept(x: Bool, l: Bool, r: Bool, kl: {l == True{} : Bool}, kr: {r == False{} : Bool}) -> {Bool.or(x, Bool.and(l, Bool.not(r))) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      match l:
        case True{}:
          match r:
            case True{}:
              LA.pce.absurd({Bool.not(True{}) == True{} : Bool}, kr)
            case False{}:
              {==}
        case False{}:
          LA.pce.absurdF({Bool.and(False{}, Bool.not(r)) == True{} : Bool}, kl)

def pce.env_keeps_listed(+reg: List<&2, String>, +keep: List<&2, String>, base: List<&2, Env.Var>, over: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.merge(base, over)), k: {Env.listed(keep, Env.Var.name(v)) == True{} : Bool}, r: {Env.registered(reg, Env.Var.name(v)) == False{} : Bool}) -> Env.In(v, Env.child(reg, keep, base, over)):
  +n = Env.Var.name(v)
  LA.pce.in_keep(reg, keep, Env.merge(base, over), v, i, LA.pce.of_spec(reg, keep, n, pce.kept(Bool.not(Env.cred(reg, n)), Env.listed(keep, n), Env.registered(reg, n), k, r)))

def Laws.env_keeps_listed(reg, keep, base, over, v, i, k, r):
  pce.env_keeps_listed(reg, keep, base, over, v, i, k, r)

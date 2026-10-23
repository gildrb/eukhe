# eukhe: the proof of LAW env_kernel_keeps_only_listed

import Base
import ../../bend/child_env.bend as Env
import ../../LAWS.bend as Laws
import ./base.bend as LA

# The test
# --------

# a credential name passes only when kept and no provider name
def pce.only(c: Bool, +l: Bool, +r: Bool, e: {c == True{} : Bool}, +p: {Bool.or(Bool.not(c), Bool.and(l, Bool.not(r))) == True{} : Bool}) -> ({l == True{} : Bool} & {r == False{} : Bool}):
  match c:
    case True{}:
      (LA.pce.and_l(l, Bool.not(r), p), LA.pce.not_t(r, LA.pce.and_r(l, Bool.not(r), p)))
    case False{}:
      LA.pce.absurdF(({l == True{} : Bool} & {r == False{} : Bool}), e)

def pce.env_kernel_keeps_only_listed(+reg: List<&2, String>, +keep: List<&2, String>, base: List<&2, Env.Var>, over: List<&2, Env.Var>, +v: Env.Var, i: Env.In(v, Env.child(reg, keep, base, over)), c: {Env.cred(reg, Env.Var.name(v)) == True{} : Bool}) -> ({Env.listed(keep, Env.Var.name(v)) == True{} : Bool} & {Env.registered(reg, Env.Var.name(v)) == False{} : Bool}):
  +n = Env.Var.name(v)
  pce.only(Env.cred(reg, n), Env.listed(keep, n), Env.registered(reg, n), c, LA.pce.spec_of(reg, keep, n, LA.pce.child_passes(reg, keep, Env.merge(base, over), v, i)))

def Laws.env_kernel_keeps_only_listed(reg, keep, base, over, v, i, c):
  pce.env_kernel_keeps_only_listed(reg, keep, base, over, v, i, c)

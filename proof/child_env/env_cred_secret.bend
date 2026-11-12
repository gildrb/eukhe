# eukhe: the proof of LAW env_cred_secret
#
# PROOF: the upper case of n is a, p, c (LN.pcn.up_of), which holds p (LN.pcn.contains_mid); p is a pattern of the model's list (the same list as env_secrets), so the pattern test holds (LN.pcn.matched_hit).

import Base
import ../../bend/child_env.bend as Env
import ../../laws/child_env.bend as ChildEnv
import ./base/names.bend as LN

def ChildEnv.env_cred_secret(reg, n, i, p, a, c, hp, hn):
  +u = String.append(a, String.append(p, c))
  %Equal.sym(String, Env.up(n), u, LN.pcn.up_of(n, u, hn)) : {Bool.or(Env.listed(reg, _), Env.matched(Env.patterns(), _)) == True{} : Bool}
  LN.pcn.or_r(Env.listed(reg, u), Env.matched(Env.patterns(), u), LN.pcn.matched_hit(Env.patterns(), i, p, u, hp, LN.pcn.contains_mid(a, p, c)))

# eukhe: the proof of LAW env_cred_registered
#
# PROOF: the credential test is the registry test or the pattern test; the first holds.

import Base
import ../../bend/child_env.bend as Env
import ../../laws/child_env.bend as ChildEnv
import ./base/names.bend as LN

def ChildEnv.env_cred_registered(reg, n, h):
  %Equal.sym(Bool, Env.registered(reg, n), True{}, h) : {Bool.or(_, Env.matched(Env.patterns(), Env.up(n))) == True{} : Bool}
  {==}

# eukhe: the proof of LAW env_registered_name
#
# PROOF: the upper case of n is r (LN.pcn.up_of), and the registry lists r (LN.pcn.listed_name).

import Base
import ../../bend/child_env.bend as Env
import ../../laws/child_env.bend as ChildEnv
import ./base/names.bend as LN

def ChildEnv.env_registered_name(xs, r, ys, n, h):
  %Equal.sym(String, Env.up(n), r, LN.pcn.up_of(n, r, h)) : {Env.listed(List.append(&2, String, xs, r <> ys), _) == True{} : Bool}
  LN.pcn.listed_name(xs, r, ys)

# eukhe: the proof of LAW env_registered_only
#
# PROOF: the registry lists the upper case of n (LN.pcn.listed_only), which is n in ASCII upper case (LN.pcn.case_up).

import Base
import ../../bend/child_env.bend as Env
import ../../laws/child_env.bend as ChildEnv
import ./base/names.bend as LN

def pro.split(-reg: List<&2, String>, +n: String, s: LN.pcn.Split(reg, Env.up(n))) -> &xs: List<&2, String> -> &r: String -> &ys: List<&2, String> -> ({reg == List.append(&2, String, xs, r <> ys) : List<&2, String>} & ChildEnv.env_case_eq(n, r)):
  (xs, p) = s
  (ys, e) = p
  (xs, (Env.up(n), (ys, (e, LN.pcn.case_up(n)))))

def ChildEnv.env_registered_only(reg, n, h):
  pro.split(reg, n, LN.pcn.listed_only(reg, Env.up(n), h))

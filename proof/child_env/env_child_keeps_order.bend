# eukhe: the proof of LAW env_child_keeps_order
#
# PROOF: the filter's own mask (each variable's pass test) picks the filter's list (LN.pcn.pick_keep).

import Base
import ../../bend/child_env.bend as Env
import ../../laws/child_env.bend as ChildEnv
import ./base/names.bend as LN

def ChildEnv.env_child_keeps_order(reg, keep, base, over):
  (LN.pcn.mask(reg, keep, Env.merge(base, over)), LN.pcn.pick_keep(reg, keep, Env.merge(base, over)))

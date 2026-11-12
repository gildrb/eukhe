# eukhe: the proof of LAW env_listed_name
#
# PROOF: a list that holds n lists it: the scan meets n, which String.eq reads as itself (LN.pcn.listed_name).

import Base
import ../../bend/child_env.bend as Env
import ../../laws/child_env.bend as ChildEnv
import ./base/names.bend as LN

def ChildEnv.env_listed_name(xs, n, ys):
  LN.pcn.listed_name(xs, n, ys)

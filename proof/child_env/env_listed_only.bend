# eukhe: the proof of LAW env_listed_only
#
# PROOF: the scan answers True only at a name String.eq reads as n, which is n (LN.pcn.listed_only, LN.pcn.str_sound).

import Base
import ../../bend/child_env.bend as Env
import ../../laws/child_env.bend as ChildEnv
import ./base/names.bend as LN

def ChildEnv.env_listed_only(ns, n, h):
  LN.pcn.listed_only(ns, n, h)

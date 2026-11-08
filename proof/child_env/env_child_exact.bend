# eukhe: the proof of LAW env_child_exact
# Each step of the model is the spec's: the upper case, the registry and
# pattern scans, the pass test, the merge and the filter (LS.pcs.child).

import Base
import ../../bend/child_env.bend as Env
import ../../bend/ffi_child_env.bend as FEnv
import ../../bend/wire.bend as Wr
import ../../laws/child_env.bend as ChildEnv
import ./base/spec.bend as LS

def ChildEnv.env_child_exact(reg, keep, base, over):
  LS.pcs.child(reg, keep, base, over)

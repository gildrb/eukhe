# eukhe: the proof of LAW env_ffi_exact
# The entry's decoder is the spec's reader stage by stage (LS.pcs.req),
# its reply the spec's (LS.pcs.run), its errors the spec's (LS.pcs.ffi).

import Base
import ../../bend/child_env.bend as Env
import ../../bend/ffi_child_env.bend as FEnv
import ../../bend/wire.bend as Wr
import ../../laws/child_env.bend as ChildEnv
import ./base/spec.bend as LS

def ChildEnv.env_ffi_exact(s):
  LS.pcs.ffi(s)

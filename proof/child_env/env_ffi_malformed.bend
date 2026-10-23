# eukhe: the proof of LAW env_ffi_malformed

import Base
import ../../bend/ffi_child_env.bend as FEnv
import ../../bend/wire.bend as Wr
import ../../laws/child_env.bend as ChildEnv

def ChildEnv.env_ffi_malformed(s, h):
  Equal.cong(Wr.Dec<FEnv.Req>, String, d => FEnv.ffi.go(d), FEnv.get_req(s), Wr.Bad{}, h)

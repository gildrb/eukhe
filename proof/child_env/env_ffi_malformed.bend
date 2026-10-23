# eukhe: the proof of LAW env_ffi_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_child_env.bend as FEnv
import ../../LAWS.bend as Laws

def Laws.env_ffi_malformed(s, h):
  Equal.cong(Wr.Dec<FEnv.Req>, String, d => FEnv.ffi.go(d), FEnv.get_req(s), Wr.Bad{}, h)

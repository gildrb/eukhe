# eukhe: the proof of LAW env_ffi_is_child

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_child_env.bend as FEnv
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.env_ffi_is_child(r, k, b, o, h):
  Equal.cong(Wr.Dec<FEnv.Req>, String, d => FEnv.ffi.go(d), FEnv.get_req(FEnv.put_req(FEnv.Req{r, k, b, o}, "")), Wr.Got{FEnv.Req{r, k, b, o}, ""}, LA.pce.req_rt(FEnv.Req{r, k, b, o}, "", h))

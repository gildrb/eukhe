# eukhe: the proof of LAW env_ffi_left_over

import Base
import ../../bend/ffi_child_env.bend as FEnv
import ../../bend/wire.bend as Wr
import ../../laws/child_env.bend as ChildEnv

def ChildEnv.env_ffi_left_over(s, q, r, h, e):
  Equal.trans(String, FEnv.ffi.go(FEnv.get_req(s)), FEnv.ffi.go(Wr.Got{q, r}), Wr.err("child_env: input left over"), Equal.cong(Wr.Dec<FEnv.Req>, String, d => FEnv.ffi.go(d), FEnv.get_req(s), Wr.Got{q, r}, h), Equal.cong(Bool, String, b => FEnv.ffi.whole(q, b), String.is_empty(r), False{}, e))

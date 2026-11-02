# eukhe: the proof of LAW env_ffi_spelled
# The spec's spelling is the entry's encoding (LS.pcs.put_req), which the
# entry reads back whole (env_ffi_round_trip); its reply is the spec's.

import Base
import ../../bend/child_env.bend as Env
import ../../bend/ffi_child_env.bend as FEnv
import ../../bend/wire.bend as Wr
import ../../laws/child_env.bend as ChildEnv
import ./base/spec.bend as LS
import ./env_ffi_round_trip.bend as PRt

def ChildEnv.env_ffi_spelled(q, h):
  %LS.pcs.put_req(q, "") : {FEnv.ffi(_) == ChildEnv.ce_reply(q) : String}
  %Equal.sym(Wr.Dec<FEnv.Req>, FEnv.get_req(FEnv.put_req(q, "")), Wr.Got{q, ""}, ChildEnv.env_ffi_round_trip(q, "", h)) : {FEnv.ffi.go(_) == ChildEnv.ce_reply(q) : String}
  LS.pcs.run(q)

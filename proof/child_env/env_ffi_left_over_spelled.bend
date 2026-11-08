# eukhe: the proof of LAW env_ffi_left_over_spelled
#
# PROOF: the spelled request is the entry's own encoding of it (pes.req),
# which reads back whole with the rest after it (pce.req_rt); a rest that
# is not empty is input left over.

import Base
import ../../bend/ffi_child_env.bend as FEnv
import ../../bend/wire.bend as Wr
import ../../laws/child_env.bend as ChildEnv
import ./base.bend as LA
import ./env_ffi_answers_spelled/spell.bend as LS

def ChildEnv.env_ffi_left_over_spelled(q, fits, c, t):
  %LS.pes.req(q, SCon{c, t}) : {FEnv.ffi(_) == Wr.err("child_env: input left over") : String}
  %Equal.sym(Wr.Dec<FEnv.Req>, FEnv.get_req(FEnv.put_req(q, SCon{c, t})), Wr.Got{q, SCon{c, t}}, LA.pce.req_rt(q, SCon{c, t}, fits)) : {FEnv.ffi.go(_) == Wr.err("child_env: input left over") : String}
  {==}

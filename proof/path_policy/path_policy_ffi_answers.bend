# eukhe: the proof of LAW path_policy_ffi_answers

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/wire.bend as Wr
import ../../bend/ffi_path_policy.bend as FPp
import ../../LAWS.bend as Laws
import ./path_policy_ffi_request_round_trip.bend as PPathPolicyFfiRequestRoundTrip

def Laws.path_policy_ffi_answers(ro, ru, se, at, l, h):
  %Equal.sym(Wr.Dec<FPp.Req>, FPp.get_req(FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, "")), Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, ""}, Laws.path_policy_ffi_request_round_trip(ro, ru, se, at, l, "", h)) : {FPp.answer(_) == FPp.put_judged(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}), "") : String}
  {==}

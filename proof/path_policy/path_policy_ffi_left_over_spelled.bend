# eukhe: the proof of LAW path_policy_ffi_left_over_spelled
#
# PROOF: the spelled request is the entry's own writing of it
# (LA.pp.req_spell), which reads back with the char left
# (path_policy_ffi_request_round_trip); the end check sees it and answers
# the error form.

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/path_policy.bend as Pp
import ../../bend/wire.bend as Wr
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./path_policy_ffi_request_round_trip.bend as PPathPolicyFfiRequestRoundTrip

def pp.left_over_spelled(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, +l: Bool, fits: {PathPolicy.pp_req_fits(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) == True{} : Bool}, +c: Char, +t: String) -> {FPp.ffi(PathPolicy.pp_spell_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, SCon{c, t})) == Wr.err("path_policy: input left over") : String}:
  %LA.pp.req_spell(ro, ru, se, at, l, SCon{c, t}) : {FPp.ffi(_) == Wr.err("path_policy: input left over") : String}
  %Equal.sym(Wr.Dec<FPp.Req>, FPp.get_req(FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, SCon{c, t})), Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, SCon{c, t}}, PathPolicy.path_policy_ffi_request_round_trip(ro, ru, se, at, l, SCon{c, t}, LA.pp.fits_code(ro, ru, se, at, l, fits))) : {FPp.answer(_) == Wr.err("path_policy: input left over") : String}
  {==}

def PathPolicy.path_policy_ffi_left_over_spelled(q, fits, c, t):
  match q:
    case FPp.Req{p, r}:
      match p r:
        case Pp.Pol{+ro, +ru, +se} Pp.Res{+at, +l}:
          pp.left_over_spelled(ro, ru, se, at, l, fits, c, t)

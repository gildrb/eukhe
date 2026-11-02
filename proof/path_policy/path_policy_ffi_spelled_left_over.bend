# eukhe: the proof of LAW path_policy_ffi_spelled_left_over
#
# PROOF of LAW path_policy_ffi_spelled_left_over: the spec's spelling is
# the entry's encoding (pe.put), which reads back with the rest after it
# (path_policy_ffi_request_round_trip); the rest is not empty, so the
# entry answers the left-over error.

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/path_policy.bend as Pp
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/path_policy.bend as PathPolicy
import ./path_policy_ffi_request_round_trip.bend as PPathPolicyFfiRequestRoundTrip
import ./base/entry.bend as LAPathPolicyEntry

def PathPolicy.path_policy_ffi_spelled_left_over(q, rest, fit, more):
  match q:
    case FPp.Req{p, r}:
      match p r:
        case Pp.Pol{+ro, +ru, +se} Pp.Res{+at, +l}:
          +hfit = Equal.trans(Bool, LAPathPolicyEntry.pe.F(Fl.flat(ro), Fl.flat(FPp.rules(ru)), Fl.flat(se), at), PathPolicy.pp_req_fits(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}), True{}, LAPathPolicyEntry.pe.fits(ro, ru, se, at), fit)
          %LAPathPolicyEntry.pe.put(ro, ru, se, at, l, rest) : {FPp.ffi(_) == Wr.err("path_policy: input left over") : String}
          %Equal.sym(Wr.Dec<FPp.Req>, FPp.get_req(FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest)), Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest}, PathPolicy.path_policy_ffi_request_round_trip(ro, ru, se, at, l, rest, hfit)) : {FPp.answer(_) == Wr.err("path_policy: input left over") : String}
          %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FPp.reply(_, FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) == Wr.err("path_policy: input left over") : String}
          {==}

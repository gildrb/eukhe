# eukhe: the proof of LAW tiny_ffi_left_over_spelled
#
# PROOF: the spec's spelling is the entry's put_req (tas.req), which reads
# back with the rest untouched (tiny_ffi_request_round_trip); a rest that
# is not empty answers the left-over error.

import Base
import ../../bend/ffi_tiny.bend as FTn
import ../../bend/wire.bend as Wr
import ../../laws/tiny/pick.bend as Tiny
import ./tiny_ffi_request_round_trip.bend as PTinyFfiRequestRoundTrip
import ./tiny_ffi_answers_spelled.bend as PTinyFfiAnswersSpelled

def tls.main(q: FTn.Req, fits: {Tiny.tiny_req_fits(q) == True{} : Bool}, +ch: Char, +t: String) -> {FTn.ffi(Tiny.tiny_spell_req(q, SCon{ch, t})) == Wr.err("tiny: input left over") : String}:
  match q:
    case FTn.Req{+c, +u}:
      %PTinyFfiAnswersSpelled.tas.req(c, u, SCon{ch, t}) : {FTn.ffi(_) == Wr.err("tiny: input left over") : String}
      %Equal.sym(Wr.Dec<FTn.Req>, FTn.get_req(FTn.put_req(FTn.Req{c, u}, SCon{ch, t})), Wr.Got{FTn.Req{c, u}, SCon{ch, t}}, Tiny.tiny_ffi_request_round_trip(c, u, SCon{ch, t}, fits)) : {FTn.answer(_) == Wr.err("tiny: input left over") : String}
      {==}

def Tiny.tiny_ffi_left_over_spelled(q, fits, c, t):
  tls.main(q, fits, c, t)

# eukhe: the proof of LAW tools_ffi_left_over_spelled
#
# PROOF: the spec's spelling is the entry's put_req (tas.req), which reads
# back with the rest untouched (tools_ffi_request_round_trip); a rest that
# is not empty answers the left-over error.

import Base
import ../../bend/ffi_tools.bend as FTl
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/tools.bend as Tools
import ./tools_ffi_request_round_trip.bend as PToolsFfiRequestRoundTrip
import ./tools_ffi_answers_spelled.bend as PToolsFfiAnswersSpelled

def Tools.tools_ffi_left_over_spelled(gs, fits, c, t):
  %PToolsFfiAnswersSpelled.tas.req(gs, SCon{c, t}) : {FTl.ffi(_) == Wr.err("tools: input left over") : String}
  %Equal.sym(Wr.Dec<List<&2, Tl.Seg>>, FTl.get_req(FTl.put_req(gs, SCon{c, t})), Wr.Got{gs, SCon{c, t}}, Tools.tools_ffi_request_round_trip(gs, SCon{c, t}, PToolsFfiAnswersSpelled.tas.fits(gs, fits))) : {FTl.answer(_) == Wr.err("tools: input left over") : String}
  {==}

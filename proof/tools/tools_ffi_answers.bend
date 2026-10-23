# eukhe: the proof of LAW tools_ffi_answers

import Base
import ../../bend/ffi_tools.bend as FTl
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/tools.bend as Tools
import ./tools_ffi_request_round_trip.bend as PToolsFfiRequestRoundTrip

def Tools.tools_ffi_answers(gs, h):
  %Equal.sym(Wr.Dec<List<&2, Tl.Seg>>, FTl.get_req(FTl.put_req(gs, "")), Wr.Got{gs, ""}, Tools.tools_ffi_request_round_trip(gs, "", h)) : {FTl.answer(_) == FTl.put_names(Tl.resolve(gs), "") : String}
  {==}

# eukhe: the proof of LAW tiny_ffi_answers

import Base
import ../../bend/ffi_tiny.bend as FTn
import ../../bend/tiny.bend as Tn
import ../../bend/wire.bend as Wr
import ../../laws/tiny.bend as Tiny
import ./tiny_ffi_request_round_trip.bend as PTinyFfiRequestRoundTrip

def Tiny.tiny_ffi_answers(chain, up, h):
  %Equal.sym(Wr.Dec<FTn.Req>, FTn.get_req(FTn.put_req(FTn.Req{chain, up}, "")), Wr.Got{FTn.Req{chain, up}, ""}, Tiny.tiny_ffi_request_round_trip(chain, up, "", h)) : {FTn.answer(_) == FTn.put_pick(Tn.pick(chain, up), "") : String}
  {==}

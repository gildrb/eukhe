# eukhe: the proof of LAW core_infer_round_trip

import Base
import ../../bend/ffi_infer.bend as FIn
import ../../bend/wire.bend as Wr
import ../../laws/infer.bend as Infer
import ./base.bend as LA

def Infer.core_infer_round_trip(q, rest, h):
  Equal.sym(Wr.Dec<FIn.Req>, Wr.Got{q, rest}, FIn.get_req(FIn.put_req(q, rest)), LA.pc.i_req(q, rest, h))

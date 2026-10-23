# eukhe: the proof of LAW core_infer_round_trip

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_infer.bend as FIn
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.core_infer_round_trip(q, rest, h):
  Equal.sym(Wr.Dec<FIn.Req>, Wr.Got{q, rest}, FIn.get_req(FIn.put_req(q, rest)), LA.pc.i_req(q, rest, h))

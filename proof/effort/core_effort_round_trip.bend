# eukhe: the proof of LAW core_effort_round_trip

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_effort.bend as FEf
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.core_effort_round_trip(q, rest, h):
  Equal.sym(Wr.Dec<FEf.Req>, Wr.Got{q, rest}, FEf.get_req(FEf.put_req(q, rest)), LA.pc.e_req(q, rest, h))

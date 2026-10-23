# eukhe: the proof of LAW core_facts_round_trip

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_facts.bend as FFx
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.core_facts_round_trip(q, rest, h):
  Equal.sym(Wr.Dec<FFx.Req>, Wr.Got{q, rest}, FFx.get_req(FFx.put_req(q, rest)), LA.pc.f_req(q, rest, h))

# eukhe: the proof of LAW core_facts_round_trip

import Base
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ./base.bend as LA

def Facts.core_facts_round_trip(q, rest, h):
  Equal.sym(Wr.Dec<FFx.Req>, Wr.Got{q, rest}, FFx.get_req(FFx.put_req(q, rest)), LA.pc.f_req(q, rest, h))

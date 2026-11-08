# eukhe: the proof of LAW core_facts_round_trip
#
# PROOF: the grammar's spelling is the entry's writer (LA.fs.req), whose
# request reads back whole (LA.pc.f_req).

import Base
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts/budgets.bend as FactsBudgets
import ./base.bend as LA

def frt.main(+q: FFx.Req, +rest: String, +h: {FactsBudgets.core_facts_req_fits(q) == True{} : Bool}) -> {FFx.get_req(FactsBudgets.facts_spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FFx.Req>}:
  %LA.fs.req(q, rest) : {FFx.get_req(_) == Wr.Got{q, rest} : Wr.Dec<FFx.Req>}
  Equal.sym(Wr.Dec<FFx.Req>, Wr.Got{q, rest}, FFx.get_req(FFx.put_req(q, rest)), LA.pc.f_req(q, rest, h))

def FactsBudgets.core_facts_round_trip(q, rest, h):
  frt.main(q, rest, h)

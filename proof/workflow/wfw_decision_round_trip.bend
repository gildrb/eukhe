# eukhe: the proof of LAW wfw_decision_round_trip

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../bend/workflow.bend as W
import ../../laws/workflow.bend as Workflow
import ../base.bend as L
import ./base.bend as LA
import ./wfw_admit_round_trip.bend as PWfwAdmitRoundTrip

# a admit reads back (turned around for rewriting)
def pww.admit(+a: W.Admit, +rest: String, h: {Workflow.wfw_admit_fits(a) == True{} : Bool}) -> {Wr.Got{a, rest} == FW.get_admit(FW.put_admit(a, rest)) : Wr.Dec<W.Admit>}:
  Equal.sym(Wr.Dec<W.Admit>, FW.get_admit(FW.put_admit(a, rest)), Wr.Got{a, rest}, Workflow.wfw_admit_round_trip(a, rest, h))

def Workflow.wfw_decision_round_trip(a, p, rest, h):
  +z = rest
  +hh = h
  %pww.admit(a, FW.put_pool(p, z), L.wr_and_l(Workflow.wfw_admit_fits(a), Workflow.wfw_pool_fits(p), hh)) : {FW.get_decision.go(_) == Wr.Got{(a, p), z} : Wr.Dec<+Sigma<W.Admit, x => W.Pool>>}
  %LA.pww.pool(p, z, L.wr_and_r(Workflow.wfw_admit_fits(a), Workflow.wfw_pool_fits(p), hh)) : {FW.get_decision.pool(a, _) == Wr.Got{(a, p), z} : Wr.Dec<+Sigma<W.Admit, x => W.Pool>>}
  {==}

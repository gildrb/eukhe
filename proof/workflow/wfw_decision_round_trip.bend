# eukhe: the proof of LAW wfw_decision_round_trip

import Base
import ../../bend/workflow.bend as W
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA
import ./wfw_admit_round_trip.bend as PWfwAdmitRoundTrip

# a admit reads back (turned around for rewriting)
def pww.admit(+a: W.Admit, +rest: String, h: {Laws.wfw_admit_fits(a) == True{} : Bool}) -> {Wr.Got{a, rest} == FW.get_admit(FW.put_admit(a, rest)) : Wr.Dec<W.Admit>}:
  Equal.sym(Wr.Dec<W.Admit>, FW.get_admit(FW.put_admit(a, rest)), Wr.Got{a, rest}, Laws.wfw_admit_round_trip(a, rest, h))

def Laws.wfw_decision_round_trip(a, p, rest, h):
  +z = rest
  +hh = h
  %pww.admit(a, FW.put_pool(p, z), L.wr_and_l(Laws.wfw_admit_fits(a), Laws.wfw_pool_fits(p), hh)) : {FW.get_decision.go(_) == Wr.Got{(a, p), z} : Wr.Dec<+Sigma<W.Admit, x => W.Pool>>}
  %LA.pww.pool(p, z, L.wr_and_r(Laws.wfw_admit_fits(a), Laws.wfw_pool_fits(p), hh)) : {FW.get_decision.pool(a, _) == Wr.Got{(a, p), z} : Wr.Dec<+Sigma<W.Admit, x => W.Pool>>}
  {==}

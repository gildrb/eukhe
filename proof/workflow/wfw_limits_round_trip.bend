# eukhe: the proof of LAW wfw_limits_round_trip

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../bend/workflow.bend as W
import ../../laws/base.bend as LawsBase
import ../../laws/workflow.bend as Workflow
import ../base/bool/and.bend as LBoolAnd
import ./base.bend as LA

def Workflow.wfw_limits_round_trip(l, rest, h):
  match l:
    case W.Limits{+c, +m}:
      +z = rest
      +hh = h
      %LA.pww.nat(c, Wr.put_nat(m, z), LBoolAnd.wr_and_l(LawsBase.wire_fits(c), LawsBase.wire_fits(m), hh)) : {FW.get_limits.go(_) == Wr.Got{W.Limits{c, m}, z} : Wr.Dec<W.Limits>}
      %LA.pww.nat(m, z, LBoolAnd.wr_and_r(LawsBase.wire_fits(c), LawsBase.wire_fits(m), hh)) : {FW.get_limits.max(c, _) == Wr.Got{W.Limits{c, m}, z} : Wr.Dec<W.Limits>}
      {==}

# eukhe: the proof of LAW wfw_limits_round_trip

import Base
import ../../bend/workflow.bend as W
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def Laws.wfw_limits_round_trip(l, rest, h):
  match l:
    case W.Limits{+c, +m}:
      +z = rest
      +hh = h
      %LA.pww.nat(c, Wr.put_nat(m, z), L.wr_and_l(Laws.wire_fits(c), Laws.wire_fits(m), hh)) : {FW.get_limits.go(_) == Wr.Got{W.Limits{c, m}, z} : Wr.Dec<W.Limits>}
      %LA.pww.nat(m, z, L.wr_and_r(Laws.wire_fits(c), Laws.wire_fits(m), hh)) : {FW.get_limits.max(c, _) == Wr.Got{W.Limits{c, m}, z} : Wr.Dec<W.Limits>}
      {==}

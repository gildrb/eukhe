# eukhe: the proof of LAW refine_plan_fit_final_room
#
# PROOF: the code's max tokens are R8's (LFit.rpf.room).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/walk.bend as RefinePlanWalk
import ./base/fit.bend as LFit
import ./base/chars.bend as LCh

def rpfl.final_room(+w: Rp.Win, conv: Nat, +plen: Nat, +m: Nat, +ok: {RefinePlanWalk.rs_room(w, plen, m) == True{} : Bool}) -> {Rp.fit(w, conv, Rp.SFinal{}, plen) == Rp.TOk{m} : Rp.Step}:
  match w:
    case Rp.Win{+cw, +mx, +res, +sys}:
      LFit.rpf.room(cw, mx, res, sys, conv, plen, m, ok)

def RefinePlanWalk.refine_plan_fit_final_room(w, conv, plen, m, ok):
  rpfl.final_room(w, conv, plen, m, ok)

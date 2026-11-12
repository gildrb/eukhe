# eukhe: the proof of LAW refine_plan_fit_final_no_room
#
# PROOF: the code's max tokens are 0 (LFit.rpf.no_room).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/walk.bend as RefinePlanWalk
import ./base/fit.bend as LFit
import ./base/chars.bend as LCh

def rpfl.final_no_room(+w: Rp.Win, conv: Nat, +plen: Nat, no: {RefinePlanWalk.rs_no_room(w, plen) == True{} : Bool}) -> {Rp.fit(w, conv, Rp.SFinal{}, plen) == Rp.TNo{"Refinement prompt leaves no room for output in the model's context window; retry with a smaller request."} : Rp.Step}:
  match w:
    case Rp.Win{+cw, +mx, +res, +sys}:
      LFit.rpf.no_room(cw, mx, res, sys, conv, plen, no)

def RefinePlanWalk.refine_plan_fit_final_no_room(w, conv, plen, no):
  rpfl.final_no_room(w, conv, plen, no)

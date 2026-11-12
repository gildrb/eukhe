# eukhe: the proof of LAW refine_plan_fit_probe_up_last
#
# PROOF: the code's budget test is R8's (LFit.rpf.fits); within it with no room above, len is final.

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/walk.bend as RefinePlanWalk
import ./base/fit.bend as LFit
import ./base/chars.bend as LCh

def rpfl.probe_up_last(+w: Rp.Win, conv: Nat, lo: Nat, +hi: Nat, +len: Nat, +plen: Nat, fits: {RefinePlanWalk.rs_fits(w, plen) == True{} : Bool}, last: {Nat.is_lt(len, hi) == False{} : Bool}) -> {Rp.fit(w, conv, Rp.SProbe{lo, hi, len}, plen) == Rp.TTry{len, Rp.SFinal{}} : Rp.Step}:
  match w:
    case Rp.Win{+cw, +mx, +res, +sys}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(Nat.add(sys, 1024n), plen), Nat.sub(cw, Nat.min(Nat.min(mx, res), Nat.div(cw, 2n)))), RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), LFit.rpf.fits(cw, mx, res, sys, plen)) : {Rp.fit.narrow(_, lo, hi, len) == Rp.TTry{len, Rp.SFinal{}} : Rp.Step}
      %Equal.sym(Bool, RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), True{}, fits) : {Rp.fit.narrow(_, lo, hi, len) == Rp.TTry{len, Rp.SFinal{}} : Rp.Step}
      %Equal.sym(Bool, Nat.is_lt(len, hi), False{}, last) : {Rp.fit.probe.at(_, len, hi) == Rp.TTry{len, Rp.SFinal{}} : Rp.Step}
      {==}

def RefinePlanWalk.refine_plan_fit_probe_up_last(w, conv, lo, hi, len, plen, fits, last):
  rpfl.probe_up_last(w, conv, lo, hi, len, plen, fits, last)

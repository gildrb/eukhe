# eukhe: the proof of LAW refine_plan_fit_probe_down_last
#
# PROOF: the code's budget test is R8's (LFit.rpf.fits); over it with the low bound no longer below len less one, the low bound is final.

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/walk.bend as RefinePlanWalk
import ./base/fit.bend as LFit
import ./base/chars.bend as LCh

def rpfl.probe_down_last(+w: Rp.Win, conv: Nat, +lo: Nat, hi: Nat, +len: Nat, +plen: Nat, over: {RefinePlanWalk.rs_fits(w, plen) == False{} : Bool}, last: {Nat.is_lt(lo, Nat.sub(len, 1n)) == False{} : Bool}) -> {Rp.fit(w, conv, Rp.SProbe{lo, hi, len}, plen) == Rp.TTry{lo, Rp.SFinal{}} : Rp.Step}:
  match w:
    case Rp.Win{+cw, +mx, +res, +sys}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(Nat.add(sys, 1024n), plen), Nat.sub(cw, Nat.min(Nat.min(mx, res), Nat.div(cw, 2n)))), RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), LFit.rpf.fits(cw, mx, res, sys, plen)) : {Rp.fit.narrow(_, lo, hi, len) == Rp.TTry{lo, Rp.SFinal{}} : Rp.Step}
      %Equal.sym(Bool, RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), False{}, over) : {Rp.fit.narrow(_, lo, hi, len) == Rp.TTry{lo, Rp.SFinal{}} : Rp.Step}
      %Equal.sym(Bool, Nat.is_lt(lo, Nat.sub(len, 1n)), False{}, last) : {Rp.fit.probe.at(_, lo, Nat.sub(len, 1n)) == Rp.TTry{lo, Rp.SFinal{}} : Rp.Step}
      {==}

def RefinePlanWalk.refine_plan_fit_probe_down_last(w, conv, lo, hi, len, plen, over, last):
  rpfl.probe_down_last(w, conv, lo, hi, len, plen, over, last)

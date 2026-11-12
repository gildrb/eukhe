# eukhe: the proof of LAW refine_plan_fit_probe_down
#
# PROOF: the code's budget test is R8's (LFit.rpf.fits); over it the high bound falls to len less one and the search asks R8's middle (LFit.rpf.mid).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/walk.bend as RefinePlanWalk
import ./base/fit.bend as LFit
import ./base/chars.bend as LCh

def rpfl.probe_down(+w: Rp.Win, conv: Nat, +lo: Nat, hi: Nat, +len: Nat, +plen: Nat, +m: Nat, over: {RefinePlanWalk.rs_fits(w, plen) == False{} : Bool}, more: {Nat.is_lt(lo, Nat.sub(len, 1n)) == True{} : Bool}, mid: {RefinePlanWalk.rs_mid(lo, Nat.sub(len, 1n), m) == True{} : Bool}) -> {Rp.fit(w, conv, Rp.SProbe{lo, hi, len}, plen) == Rp.TTry{m, Rp.SProbe{lo, Nat.sub(len, 1n), m}} : Rp.Step}:
  match w:
    case Rp.Win{+cw, +mx, +res, +sys}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(Nat.add(sys, 1024n), plen), Nat.sub(cw, Nat.min(Nat.min(mx, res), Nat.div(cw, 2n)))), RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), LFit.rpf.fits(cw, mx, res, sys, plen)) : {Rp.fit.narrow(_, lo, hi, len) == Rp.TTry{m, Rp.SProbe{lo, Nat.sub(len, 1n), m}} : Rp.Step}
      %Equal.sym(Bool, RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), False{}, over) : {Rp.fit.narrow(_, lo, hi, len) == Rp.TTry{m, Rp.SProbe{lo, Nat.sub(len, 1n), m}} : Rp.Step}
      %Equal.sym(Bool, Nat.is_lt(lo, Nat.sub(len, 1n)), True{}, more) : {Rp.fit.probe.at(_, lo, Nat.sub(len, 1n)) == Rp.TTry{m, Rp.SProbe{lo, Nat.sub(len, 1n), m}} : Rp.Step}
      %Equal.sym(Nat, Nat.div(Nat.add(Nat.add(lo, Nat.sub(len, 1n)), 1n), 2n), m, LFit.rpf.mid(lo, Nat.sub(len, 1n), m, mid)) : {Rp.TTry{_, Rp.SProbe{lo, Nat.sub(len, 1n), _}} == Rp.TTry{m, Rp.SProbe{lo, Nat.sub(len, 1n), m}} : Rp.Step}
      {==}

def RefinePlanWalk.refine_plan_fit_probe_down(w, conv, lo, hi, len, plen, m, over, more, mid):
  rpfl.probe_down(w, conv, lo, hi, len, plen, m, over, more, mid)

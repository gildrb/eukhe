# eukhe: the proof of LAW refine_plan_fit_probe_up
#
# PROOF: the code's budget test is R8's (LFit.rpf.fits); within it the low bound rises to len and the search asks R8's middle (LFit.rpf.mid).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/walk.bend as RefinePlanWalk
import ./base/fit.bend as LFit
import ./base/chars.bend as LCh

def rpfl.probe_up(+w: Rp.Win, conv: Nat, lo: Nat, +hi: Nat, +len: Nat, +plen: Nat, +m: Nat, fits: {RefinePlanWalk.rs_fits(w, plen) == True{} : Bool}, more: {Nat.is_lt(len, hi) == True{} : Bool}, mid: {RefinePlanWalk.rs_mid(len, hi, m) == True{} : Bool}) -> {Rp.fit(w, conv, Rp.SProbe{lo, hi, len}, plen) == Rp.TTry{m, Rp.SProbe{len, hi, m}} : Rp.Step}:
  match w:
    case Rp.Win{+cw, +mx, +res, +sys}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(Nat.add(sys, 1024n), plen), Nat.sub(cw, Nat.min(Nat.min(mx, res), Nat.div(cw, 2n)))), RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), LFit.rpf.fits(cw, mx, res, sys, plen)) : {Rp.fit.narrow(_, lo, hi, len) == Rp.TTry{m, Rp.SProbe{len, hi, m}} : Rp.Step}
      %Equal.sym(Bool, RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), True{}, fits) : {Rp.fit.narrow(_, lo, hi, len) == Rp.TTry{m, Rp.SProbe{len, hi, m}} : Rp.Step}
      %Equal.sym(Bool, Nat.is_lt(len, hi), True{}, more) : {Rp.fit.probe.at(_, len, hi) == Rp.TTry{m, Rp.SProbe{len, hi, m}} : Rp.Step}
      %Equal.sym(Nat, Nat.div(Nat.add(Nat.add(len, hi), 1n), 2n), m, LFit.rpf.mid(len, hi, m, mid)) : {Rp.TTry{_, Rp.SProbe{len, hi, _}} == Rp.TTry{m, Rp.SProbe{len, hi, m}} : Rp.Step}
      {==}

def RefinePlanWalk.refine_plan_fit_probe_up(w, conv, lo, hi, len, plen, m, fits, more, mid):
  rpfl.probe_up(w, conv, lo, hi, len, plen, m, fits, more, mid)

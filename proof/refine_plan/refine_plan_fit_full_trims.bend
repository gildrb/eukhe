# eukhe: the proof of LAW refine_plan_fit_full_trims
#
# PROOF: the code's budget test is R8's (LFit.rpf.fits); over it with a conversation the search starts at R8's middle (LFit.rpf.mid).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/walk.bend as RefinePlanWalk
import ./base/fit.bend as LFit
import ./base/chars.bend as LCh

def rpfl.full_trims(+w: Rp.Win, +conv: Nat, +plen: Nat, +m: Nat, over: {RefinePlanWalk.rs_fits(w, plen) == False{} : Bool}, +some: {Nat.is_eq(conv, 0n) == False{} : Bool}, mid: {RefinePlanWalk.rs_mid(0n, conv, m) == True{} : Bool}) -> {Rp.fit(w, conv, Rp.SFull{}, plen) == Rp.TTry{m, Rp.SProbe{0n, conv, m}} : Rp.Step}:
  match w:
    case Rp.Win{+cw, +mx, +res, +sys}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(Nat.add(sys, 1024n), plen), Nat.sub(cw, Nat.min(Nat.min(mx, res), Nat.div(cw, 2n)))), RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), LFit.rpf.fits(cw, mx, res, sys, plen)) : {Rp.fit.full(Bool.and(Bool.not(_), Bool.not(Nat.is_eq(conv, 0n))), conv, Rp.fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(Nat.add(sys, 1024n), plen))))) == Rp.TTry{m, Rp.SProbe{0n, conv, m}} : Rp.Step}
      %Equal.sym(Bool, RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), False{}, over) : {Rp.fit.full(Bool.and(Bool.not(_), Bool.not(Nat.is_eq(conv, 0n))), conv, Rp.fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(Nat.add(sys, 1024n), plen))))) == Rp.TTry{m, Rp.SProbe{0n, conv, m}} : Rp.Step}
      %Equal.sym(Bool, Nat.is_eq(conv, 0n), False{}, some) : {Rp.fit.full(Bool.and(True{}, Bool.not(_)), conv, Rp.fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(Nat.add(sys, 1024n), plen))))) == Rp.TTry{m, Rp.SProbe{0n, conv, m}} : Rp.Step}
      %Equal.sym(Bool, Nat.is_lt(0n, conv), True{}, LFit.rpf.some(conv, some)) : {Rp.fit.probe.at(_, 0n, conv) == Rp.TTry{m, Rp.SProbe{0n, conv, m}} : Rp.Step}
      %Equal.sym(Nat, Nat.div(Nat.add(conv, 1n), 2n), m, LFit.rpf.mid(0n, conv, m, mid)) : {Rp.TTry{_, Rp.SProbe{0n, conv, _}} == Rp.TTry{m, Rp.SProbe{0n, conv, m}} : Rp.Step}
      {==}

def RefinePlanWalk.refine_plan_fit_full_trims(w, conv, plen, m, over, some, mid):
  rpfl.full_trims(w, conv, plen, m, over, some, mid)

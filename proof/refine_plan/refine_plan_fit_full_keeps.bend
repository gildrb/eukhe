# eukhe: the proof of LAW refine_plan_fit_full_keeps
#
# PROOF: the code's budget test is R8's (LFit.rpf.fits); within it or with no conversation, no trim.

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/walk.bend as RefinePlanWalk
import ./base/fit.bend as LFit
import ./base/chars.bend as LCh

def rpfl.keep(f: Bool, z: Bool, h: {Bool.or(f, z) == True{} : Bool}, +conv: Nat, +r: Rp.Step) -> {Rp.fit.full(Bool.and(Bool.not(f), Bool.not(z)), conv, r) == r : Rp.Step}:
  match f:
    case True{}:
      {==}
    case False{}:
      match z:
        case True{}:
          {==}
        case False{}:
          LCh.absurdF({Rp.fit.full(Bool.and(True{}, True{}), conv, r) == r : Rp.Step}, h)

def rpfl.full_keeps(+w: Rp.Win, +conv: Nat, +plen: Nat, keep: {Bool.or(RefinePlanWalk.rs_fits(w, plen), Nat.is_eq(conv, 0n)) == True{} : Bool}) -> {Rp.fit(w, conv, Rp.SFull{}, plen) == Rp.fit(w, conv, Rp.SFinal{}, plen) : Rp.Step}:
  match w:
    case Rp.Win{+cw, +mx, +res, +sys}:
      %Equal.sym(Bool, Nat.is_le(Nat.add(Nat.add(sys, 1024n), plen), Nat.sub(cw, Nat.min(Nat.min(mx, res), Nat.div(cw, 2n)))), RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), LFit.rpf.fits(cw, mx, res, sys, plen)) : {Rp.fit.full(Bool.and(Bool.not(_), Bool.not(Nat.is_eq(conv, 0n))), conv, Rp.fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(Nat.add(sys, 1024n), plen))))) == Rp.fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(Nat.add(sys, 1024n), plen)))) : Rp.Step}
      rpfl.keep(RefinePlanWalk.rs_fits(Rp.Win{cw, mx, res, sys}, plen), Nat.is_eq(conv, 0n), keep, conv, Rp.fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(Nat.add(sys, 1024n), plen)))))

def RefinePlanWalk.refine_plan_fit_full_keeps(w, conv, plen, keep):
  rpfl.full_keeps(w, conv, plen, keep)

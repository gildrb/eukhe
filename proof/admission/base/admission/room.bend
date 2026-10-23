# eukhe: lemmas the proofs of area admission share: admission/room

import Base
import ../../../../bend/admission.bend as Ad
import ./bit.bend as LAAdmissionBit
import ./cnt.bend as LAAdmissionCnt
import ./hit.bend as LAAdmissionHit
import ./pick.bend as LAAdmissionPick
import ../bool.bend as LABool
import ../logic.bend as LALogic

def ad.room0(+l: Ad.Lim, +hi: Nat, +w: Nat, +hb: Nat, +wb: Nat, +h: {LALogic.ad.ok.n(l, hi, 1n+w, hb, wb) == True{} : Bool}) -> {Ad.room(l, Nat.add(hi, 0n)) == False{} : Bool}:
  +cn = Ad.calm.n(hi, 1n+w, hb)
  %LABool.ad.calm_hb0(hi, w, hb, LALogic.ad.and_r(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, Nat.add(hi, hb)), 1n+w, hi, wb))), cn, h)) : {Ad.room(l, Nat.add(hi, _)) == False{} : Bool}
  LALogic.ad.ok_room(Ad.room(l, Nat.add(hi, hb)), w, hi, wb, cn, h)

def ad.adm_ia(+l: Ad.Lim, +q: Nat, +wi: Nat, +hi: Nat, +hb: Nat, +wb: Nat, +wb1: Nat, +h: {LALogic.ad.ok.n(l, hi, wi, hb, wb) == True{} : Bool}) -> {LALogic.ad.ok.n(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))}), wi), 0n, wb1) == True{} : Bool}:
  match wi:
    case 0n:
      LAAdmissionPick.ad.adm_ia0(l, hi, wb1, Ad.room(l, hi), Ad.le(q, 0n), {==})
    case 1n+w:
      LAAdmissionBit.ad.adm_ia1(l, hi, w, wb1, Ad.le(q, 1n+w), ad.room0(l, hi, w, hb, wb, h))

def ad.adm_ia_ok(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +h: {LALogic.ad.ok(l, ts) == True{} : Bool}) -> {LALogic.ad.ok(l, Ad.admit.ia(l, q, ts)) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
  +st = Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))
  +x = {Ad.Tk{Ad.Ia{}, st} : Ad.Tk}
  +t1 = Ad.preempt(ts)
  +t2 = List.append(&2, Ad.Tk, t1, [x])
  LALogic.ad.ok.tr(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, x), wi), 0n, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), hi), LAAdmissionHit.ad.app_pre(Ad.Holding{}, ts, x)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, x), wi), LAAdmissionHit.ad.app_pre(Ad.Waiting{}, ts, x)), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), 0n, Equal.trans(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t1), 0n, LAAdmissionCnt.ad.app_off(Ad.Holding{}, Ad.Bg{}, t1, x, LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, st))), LAAdmissionHit.ad.pre_hb(ts))), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), LAAdmissionCnt.ad.app_off(Ad.Waiting{}, Ad.Bg{}, t1, x, LABool.ad.and_f(Ad.Mode.of(Ad.Waiting{}, st)))), ad.adm_ia(l, q, wi, hi, hb, wb, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), h))

# eukhe: lemmas the proofs of area admission share: admission/room

import Base
import ../../../../bend/admission.bend as Ad
import ./bit.bend as LAAdmissionBit
import ./cnt.bend as LAAdmissionCnt
import ./hit.bend as LAAdmissionHit
import ./pick.bend as LAAdmissionPick
import ../bool.bend as LABool
import ../logic.bend as LALogic
import ./terms.bend as AT

def ad.room0(+l: Ad.Lim, +hi: Nat, +w: Nat, +hb: Nat, +wb: Nat, +h: {LALogic.ad.ok.n(l, hi, 1n+w, hb, wb) == True{} : Bool}) -> {Ad.room(l, Nat.add(hi, 0n)) == False{} : Bool}:
  +cn = AT.calm.n(1n+w, hb)
  %LABool.ad.calm_hb0(w, hb, LALogic.ad.and_r(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, Nat.add(hi, hb)), 1n+w, hi, wb))), cn, h)) : {Ad.room(l, Nat.add(hi, _)) == False{} : Bool}
  LALogic.ad.ok_room(Ad.room(l, Nat.add(hi, hb)), w, hi, wb, cn, h)

def ad.adm_ia(+l: Ad.Lim, +q: Nat, +wi: Nat, +hi: Nat, +hb: Nat, +wb: Nat, +wb1: Nat, +h: {LALogic.ad.ok.n(l, hi, wi, hb, wb) == True{} : Bool}) -> {LALogic.ad.ok.n(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))}), wi), 0n, wb1) == True{} : Bool}:
  match wi:
    case 0n:
      LAAdmissionPick.ad.adm_ia0(l, hi, wb1, Ad.room(l, hi), Ad.le(q, 0n), {==})
    case 1n+w:
      LAAdmissionBit.ad.adm_ia1(l, hi, w, wb1, Ad.le(q, 1n+w), ad.room0(l, hi, w, hb, wb, h))

# on a capped provider: after the preemption no background slot is held
def ad.adm_ia_pre(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +h: {LALogic.ad.ok(l, ts) == True{} : Bool}) -> {LALogic.ad.ok(l, List.append(&2, Ad.Tk, Ad.preempt(ts), [Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)))}])) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
  +st = Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))
  +x = {Ad.Tk{Ad.Ia{}, st} : Ad.Tk}
  +t1 = Ad.preempt(ts)
  +t2 = List.append(&2, Ad.Tk, t1, [x])
  LALogic.ad.ok.tr(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, x), wi), 0n, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), hi), LAAdmissionHit.ad.app_pre(Ad.Holding{}, ts, x)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, x), wi), LAAdmissionHit.ad.app_pre(Ad.Waiting{}, ts, x)), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), 0n, Equal.trans(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t1), 0n, LAAdmissionCnt.ad.app_off(Ad.Holding{}, Ad.Bg{}, t1, x, LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, st))), LAAdmissionHit.ad.pre_hb(ts))), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), LAAdmissionCnt.ad.app_off(Ad.Waiting{}, Ad.Bg{}, t1, x, LABool.ad.and_f(Ad.Mode.of(Ad.Waiting{}, st)))), ad.adm_ia(l, q, wi, hi, hb, wb, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), h))

# on an unlimited provider no interactive request waits, so the new one
# holds a slot, and the background slots it leaves held keep none from it
def ad.adm_ia_unl.n(+hi: Nat, wi: Nat, +hb: Nat, +wb: Nat, +q: Nat, h: {LALogic.ad.ok.n(Ad.Unl{}, hi, wi, hb, wb) == True{} : Bool}) -> {LALogic.ad.ok.n(Ad.Unl{}, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(Ad.Unl{}, hi)), Ad.le(q, wi))}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(Ad.Unl{}, hi)), Ad.le(q, wi))}), wi), hb, wb) == True{} : Bool}:
  match wi:
    case 0n:
      LABool.ad.or_t(Ad.isz(hb))
    case 1n+w:
      LALogic.ad.absurd({LALogic.ad.ok.n(Ad.Unl{}, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(False{}, Ad.le(q, 1n+w))}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(False{}, Ad.le(q, 1n+w))}), 1n+w), hb, wb) == True{} : Bool}, h)

def ad.adm_ia_unl(+q: Nat, +ts: List<&2, Ad.Tk>, +h: {LALogic.ad.ok(Ad.Unl{}, ts) == True{} : Bool}) -> {LALogic.ad.ok(Ad.Unl{}, Ad.admit.ia(Ad.Unl{}, q, ts)) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
  +st = Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(Ad.Unl{}, hi)), Ad.le(q, wi))
  +x = {Ad.Tk{Ad.Ia{}, st} : Ad.Tk}
  +t2 = List.append(&2, Ad.Tk, ts, [x])
  LALogic.ad.ok.tr(Ad.Unl{}, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, x), wi), hb, wb, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), hi), LAAdmissionCnt.ad.cnt_app(Ad.Holding{}, Ad.Ia{}, ts, x)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, x), wi), LAAdmissionCnt.ad.cnt_app(Ad.Waiting{}, Ad.Ia{}, ts, x)), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), hb, LAAdmissionCnt.ad.app_off(Ad.Holding{}, Ad.Bg{}, ts, x, LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, st)))), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), wb, LAAdmissionCnt.ad.app_off(Ad.Waiting{}, Ad.Bg{}, ts, x, LABool.ad.and_f(Ad.Mode.of(Ad.Waiting{}, st)))), ad.adm_ia_unl.n(hi, wi, hb, wb, q, h))

def ad.adm_ia_ok(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +h: {LALogic.ad.ok(l, ts) == True{} : Bool}) -> {LALogic.ad.ok(l, Ad.admit.ia(l, q, ts)) == True{} : Bool}:
  match l:
    case Ad.Unl{}:
      ad.adm_ia_unl(q, ts, h)
    case Ad.Cap{+p}:
      ad.adm_ia_pre(Ad.Cap{p}, q, ts, h)

# eukhe: lemmas the proofs of area admission share: admission/calm

import Base
import ../../../../bend/admission.bend as Ad
import ./bit.bend as LAAdmissionBit
import ./misc.bend as LAAdmissionMisc
import ../bool.bend as LABool

def ad.calm.tr(-a1: Nat, -a2: Nat, -a3: Nat, -b1: Nat, -b2: Nat, -b3: Nat, e1: {a1 == b1 : Nat}, e2: {a2 == b2 : Nat}, e3: {a3 == b3 : Nat}, h: {Ad.calm.n(a1, a2, a3) == True{} : Bool}) -> {Ad.calm.n(b1, b2, b3) == True{} : Bool}:
  %e1 : {Ad.calm.n(_, b2, b3) == True{} : Bool}
  %e2 : {Ad.calm.n(a1, _, b3) == True{} : Bool}
  %e3 : {Ad.calm.n(a1, a2, _) == True{} : Bool}
  h

# calm stays calm as counts drop
def ad.calm_m1(-a: Nat, -b: Nat, c: Nat, h: {Ad.calm.n(1n+a, b, c) == True{} : Bool}) -> {Ad.calm.n(a, b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      LABool.ad.absurd({Ad.calm.n(a, b, 1n+x) == True{} : Bool}, h)

def ad.calm_m2(+a: Nat, -b: Nat, c: Nat, h: {Ad.calm.n(a, 1n+b, c) == True{} : Bool}) -> {Ad.calm.n(a, b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      LABool.ad.absurd({Ad.calm.n(a, b, 1n+x) == True{} : Bool}, Equal.trans(Bool, False{}, Bool.and(Ad.isz(a), False{}), True{}, Equal.sym(Bool, Bool.and(Ad.isz(a), False{}), False{}, LABool.ad.and_f(Ad.isz(a))), h))

def ad.calm_m3(-a: Nat, -b: Nat, c: Nat, h: {Ad.calm.n(a, b, 1n+c) == True{} : Bool}) -> {Ad.calm.n(a, b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      h

def ad.calm_mono(x1: Bool, x2: Bool, x3: Bool, +a: Nat, +b: Nat, +c: Nat, h: {Ad.calm.n(Ad.bit(x1, a), Ad.bit(x2, b), Ad.bit(x3, c)) == True{} : Bool}) -> {Ad.calm.n(a, b, c) == True{} : Bool}:
  match x1 x2 x3:
    case False{} False{} False{}:
      h
    case False{} False{} True{}:
      ad.calm_m3(a, b, c, h)
    case False{} True{} False{}:
      ad.calm_m2(a, b, c, h)
    case False{} True{} True{}:
      ad.calm_m3(a, b, c, ad.calm_m2(a, b, 1n+c, h))
    case True{} False{} False{}:
      ad.calm_m1(a, b, c, h)
    case True{} False{} True{}:
      ad.calm_m3(a, b, c, ad.calm_m1(a, b, 1n+c, h))
    case True{} True{} False{}:
      ad.calm_m2(a, b, c, ad.calm_m1(a, 1n+b, c, h))
    case True{} True{} True{}:
      ad.calm_m3(a, b, c, ad.calm_m2(a, b, 1n+c, ad.calm_m1(a, 1n+b, 1n+c, h)))

# an interactive waiter: no background slot is held
def ad.calm_hb0(+hi: Nat, -w: Nat, hb: Nat, c: {Ad.calm.n(hi, 1n+w, hb) == True{} : Bool}) -> {hb == 0n : Nat}:
  match hb:
    case 0n:
      {==}
    case 1n+x:
      LABool.ad.absurd({1n+x == 0n : Nat}, Equal.trans(Bool, False{}, Bool.and(Ad.isz(hi), False{}), True{}, Equal.sym(Bool, Bool.and(Ad.isz(hi), False{}), False{}, LABool.ad.and_f(Ad.isz(hi))), c))

# A grant keeps the invariant
# ---------------------------

def ad.ok_idle(+l: Ad.Lim, +hi: Nat, +hb: Nat, c: {Ad.calm.n(hi, 0n, hb) == True{} : Bool}) -> {LABool.ad.ok.n(l, hi, 0n, hb, 0n) == True{} : Bool}:
  +r = Ad.room(l, Nat.add(hi, hb))
  %Equal.sym(Maybe<&2, Ad.Cls>, Ad.pick.go(r, 0n, hi, 0n), None{}, LAAdmissionMisc.ad.pick_none0(r, hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(hi, 0n, hb)) == True{} : Bool}
  c

def ad.grant_idle(+l: Ad.Lim, +t: List<&2, Ad.Tk>, z: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t) == 0n : Nat}, cm: {Ad.calm(t) == True{} : Bool}) -> {LABool.ad.ok(l, t) == True{} : Bool}:
  (+zi, zb) = z
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)
  LABool.ad.ok.tr(l, hi, 0n, hb, 0n, hi, wi, hb, wb, {==}, Equal.sym(Nat, wi, 0n, zi), {==}, Equal.sym(Nat, wb, 0n, zb), ad.ok_idle(l, hi, hb, ad.calm.tr(hi, wi, hb, hi, 0n, hb, {==}, zi, {==}, cm)))

def ad.calm_ia(-a: Nat, -b: Nat, hb: Nat, +hi: Nat, -w: Nat, c: {Ad.calm.n(hi, 1n+w, hb) == True{} : Bool}) -> {Ad.calm.n(a, b, hb) == True{} : Bool}:
  match hb:
    case 0n:
      {==}
    case 1n+x:
      LABool.ad.absurd({Ad.calm.n(a, b, 1n+x) == True{} : Bool}, Equal.trans(Bool, False{}, Bool.and(Ad.isz(hi), False{}), True{}, Equal.sym(Bool, Bool.and(Ad.isz(hi), False{}), False{}, LABool.ad.and_f(Ad.isz(hi))), c))

def ad.calm_mark_ia(+t: List<&2, Ad.Tk>, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)) == False{} : Bool}, cm: {Ad.calm(t) == True{} : Bool}) -> {Ad.calm(Ad.mark(Ad.Ia{}, t)) == True{} : Bool}:
  +t2 = Ad.mark(Ad.Ia{}, t)
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)
  +hi2 = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2)
  +wi2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +hb2 = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)
  %Equal.sym(Nat, hb2, hb, LAAdmissionBit.ad.cnt_mark(Ad.Holding{}, Ad.Bg{}, t, Ad.Ia{}, nz)) : {Ad.calm.n(hi2, wi2, _) == True{} : Bool}
  ad.calm_ia(hi2, wi2, hb, hi, wi2, ad.calm.tr(hi, wi, hb, hi, 1n+wi2, hb, {==}, Equal.sym(Nat, 1n+wi2, wi, LAAdmissionBit.ad.cnt_mark(Ad.Waiting{}, Ad.Ia{}, t, Ad.Ia{}, nz)), {==}, cm))

def ad.calm_bg(+t: List<&2, Ad.Tk>, zi: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat}, zh: {Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat}, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}) -> {Ad.calm(Ad.mark(Ad.Bg{}, t)) == True{} : Bool}:
  +t2 = Ad.mark(Ad.Bg{}, t)
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +hi2 = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2)
  +wi2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +hb2 = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)
  %Equal.sym(Nat, hi2, hi, LAAdmissionBit.ad.cnt_mark(Ad.Holding{}, Ad.Ia{}, t, Ad.Bg{}, nz)) : {Ad.calm.n(_, wi2, hb2) == True{} : Bool}
  %Equal.sym(Nat, wi2, wi, LAAdmissionBit.ad.cnt_mark(Ad.Waiting{}, Ad.Ia{}, t, Ad.Bg{}, nz)) : {Ad.calm.n(hi, _, hb2) == True{} : Bool}
  %Equal.sym(Nat, hi, 0n, zh) : {Ad.calm.n(_, wi, hb2) == True{} : Bool}
  %Equal.sym(Nat, wi, 0n, zi) : {Ad.calm.n(0n, _, hb2) == True{} : Bool}
  LABool.ad.or_t(Ad.isz(hb2))

def ad.end_calm(+ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, +s: Ad.Sts, +e: {Ad.get(ts, k) == Some{Ad.Tk{c, s}} : Maybe<&2, Ad.Tk>}, cm: {Ad.calm(ts) == True{} : Bool}) -> {Ad.calm(Ad.put(ts, k, Ad.Ended{})) == True{} : Bool}:
  +t2 = Ad.put(ts, k, Ad.Ended{})
  +x = {Ad.Tk{c, s} : Ad.Tk}
  +x1 = Ad.hit(Ad.Holding{}, Ad.Ia{}, x)
  +x2 = Ad.hit(Ad.Waiting{}, Ad.Ia{}, x)
  +x3 = Ad.hit(Ad.Holding{}, Ad.Bg{}, x)
  +a1 = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2)
  +a2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +a3 = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)
  ad.calm_mono(x1, x2, x3, a1, a2, a3, ad.calm.tr(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), Ad.bit(x1, a1), Ad.bit(x2, a2), Ad.bit(x3, a3), Equal.sym(Nat, Ad.bit(x1, a1), Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, s, e)), Equal.sym(Nat, Ad.bit(x2, a2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Waiting{}, Ad.Ia{}, ts, k, c, s, e)), Equal.sym(Nat, Ad.bit(x3, a3), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, s, e)), cm))

def ad.calm_of(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, h: {LABool.ad.ok(l, ts) == True{} : Bool}) -> {Ad.calm(ts) == True{} : Bool}:
  LABool.ad.and_r(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick(l, ts))), Ad.calm(ts), h)

def ad.room0(+l: Ad.Lim, +hi: Nat, +w: Nat, +hb: Nat, +wb: Nat, +h: {LABool.ad.ok.n(l, hi, 1n+w, hb, wb) == True{} : Bool}) -> {Ad.room(l, Nat.add(hi, 0n)) == False{} : Bool}:
  +cn = Ad.calm.n(hi, 1n+w, hb)
  %ad.calm_hb0(hi, w, hb, LABool.ad.and_r(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, Nat.add(hi, hb)), 1n+w, hi, wb))), cn, h)) : {Ad.room(l, Nat.add(hi, _)) == False{} : Bool}
  LABool.ad.ok_room(Ad.room(l, Nat.add(hi, hb)), w, hi, wb, cn, h)

def ad.adm_ia(+l: Ad.Lim, +q: Nat, +wi: Nat, +hi: Nat, +hb: Nat, +wb: Nat, +wb1: Nat, +h: {LABool.ad.ok.n(l, hi, wi, hb, wb) == True{} : Bool}) -> {LABool.ad.ok.n(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))}), wi), 0n, wb1) == True{} : Bool}:
  match wi:
    case 0n:
      LAAdmissionBit.ad.adm_ia0(l, hi, wb1, Ad.room(l, hi), Ad.le(q, 0n), {==})
    case 1n+w:
      LAAdmissionBit.ad.adm_ia1(l, hi, w, wb1, Ad.le(q, 1n+w), ad.room0(l, hi, w, hb, wb, h))

def ad.adm_ia_ok(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +h: {LABool.ad.ok(l, ts) == True{} : Bool}) -> {LABool.ad.ok(l, Ad.admit.ia(l, q, ts)) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
  +st = Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))
  +x = {Ad.Tk{Ad.Ia{}, st} : Ad.Tk}
  +t1 = Ad.preempt(ts)
  +t2 = List.append(&2, Ad.Tk, t1, [x])
  LABool.ad.ok.tr(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, x), wi), 0n, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), hi), LAAdmissionBit.ad.app_pre(Ad.Holding{}, ts, x)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, x), wi), LAAdmissionBit.ad.app_pre(Ad.Waiting{}, ts, x)), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), 0n, Equal.trans(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t1), 0n, LAAdmissionBit.ad.app_off(Ad.Holding{}, Ad.Bg{}, t1, x, LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, st))), LAAdmissionMisc.ad.pre_hb(ts))), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), LAAdmissionBit.ad.app_off(Ad.Waiting{}, Ad.Bg{}, t1, x, LABool.ad.and_f(Ad.Mode.of(Ad.Waiting{}, st)))), ad.adm_ia(l, q, wi, hi, hb, wb, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), h))

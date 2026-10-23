# eukhe: lemmas the proofs of area admission share: admission/calm

import Base
import ../../../../bend/admission.bend as Ad
import ./bit.bend as LAAdmissionBit
import ../bool.bend as LABool
import ../logic.bend as LALogic

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
      LALogic.ad.absurd({Ad.calm.n(a, b, 1n+x) == True{} : Bool}, h)

def ad.calm_m2(+a: Nat, -b: Nat, c: Nat, h: {Ad.calm.n(a, 1n+b, c) == True{} : Bool}) -> {Ad.calm.n(a, b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      LALogic.ad.absurd({Ad.calm.n(a, b, 1n+x) == True{} : Bool}, Equal.trans(Bool, False{}, Bool.and(Ad.isz(a), False{}), True{}, Equal.sym(Bool, Bool.and(Ad.isz(a), False{}), False{}, LABool.ad.and_f(Ad.isz(a))), h))

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

def ad.calm_ia(-a: Nat, -b: Nat, hb: Nat, +hi: Nat, -w: Nat, c: {Ad.calm.n(hi, 1n+w, hb) == True{} : Bool}) -> {Ad.calm.n(a, b, hb) == True{} : Bool}:
  match hb:
    case 0n:
      {==}
    case 1n+x:
      LALogic.ad.absurd({Ad.calm.n(a, b, 1n+x) == True{} : Bool}, Equal.trans(Bool, False{}, Bool.and(Ad.isz(hi), False{}), True{}, Equal.sym(Bool, Bool.and(Ad.isz(hi), False{}), False{}, LABool.ad.and_f(Ad.isz(hi))), c))

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

def ad.calm_of(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, h: {LALogic.ad.ok(l, ts) == True{} : Bool}) -> {Ad.calm(ts) == True{} : Bool}:
  LALogic.ad.and_r(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick(l, ts))), Ad.calm(ts), h)

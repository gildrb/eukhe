# eukhe: lemmas the proofs of area admission share: admission/calm

import Base
import ../../../../bend/admission.bend as Ad
import ./bit.bend as LAAdmissionBit
import ../bool.bend as LABool
import ../logic.bend as LALogic
import ./terms.bend as AT

def ad.calm.tr(-a2: Nat, -a3: Nat, -b2: Nat, -b3: Nat, e2: {a2 == b2 : Nat}, e3: {a3 == b3 : Nat}, h: {AT.calm.n(a2, a3) == True{} : Bool}) -> {AT.calm.n(b2, b3) == True{} : Bool}:
  %e2 : {AT.calm.n(_, b3) == True{} : Bool}
  %e3 : {AT.calm.n(a2, _) == True{} : Bool}
  h

# calm stays calm as counts drop
def ad.calm_m2(-b: Nat, c: Nat, h: {AT.calm.n(1n+b, c) == True{} : Bool}) -> {AT.calm.n(b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      LALogic.ad.absurd({AT.calm.n(b, 1n+x) == True{} : Bool}, h)

def ad.calm_m3(-b: Nat, c: Nat, h: {AT.calm.n(b, 1n+c) == True{} : Bool}) -> {AT.calm.n(b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      h

def ad.calm_mono(x2: Bool, x3: Bool, +b: Nat, +c: Nat, h: {AT.calm.n(Ad.bit(x2, b), Ad.bit(x3, c)) == True{} : Bool}) -> {AT.calm.n(b, c) == True{} : Bool}:
  match x2 x3:
    case False{} False{}:
      h
    case False{} True{}:
      ad.calm_m3(b, c, h)
    case True{} False{}:
      ad.calm_m2(b, c, h)
    case True{} True{}:
      ad.calm_m3(b, c, ad.calm_m2(b, 1n+c, h))

# an interactive waiter: no background slot is held, so calm with any
# waiters
def ad.calm_ia(-b: Nat, hb: Nat, -w: Nat, c: {AT.calm.n(1n+w, hb) == True{} : Bool}) -> {AT.calm.n(b, hb) == True{} : Bool}:
  match hb:
    case 0n:
      {==}
    case 1n+x:
      LALogic.ad.absurd({AT.calm.n(b, 1n+x) == True{} : Bool}, c)

def ad.calm_mark_ia(+t: List<&2, Ad.Tk>, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)) == False{} : Bool}, cm: {AT.calm(t) == True{} : Bool}) -> {AT.calm(Ad.mark(Ad.Ia{}, t)) == True{} : Bool}:
  +t2 = Ad.mark(Ad.Ia{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)
  +wi2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +hb2 = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)
  %Equal.sym(Nat, hb2, hb, LAAdmissionBit.ad.cnt_mark(Ad.Holding{}, Ad.Bg{}, t, Ad.Ia{}, nz)) : {AT.calm.n(wi2, _) == True{} : Bool}
  ad.calm_ia(wi2, hb, wi2, ad.calm.tr(wi, hb, 1n+wi2, hb, Equal.sym(Nat, 1n+wi2, wi, LAAdmissionBit.ad.cnt_mark(Ad.Waiting{}, Ad.Ia{}, t, Ad.Ia{}, nz)), {==}, cm))

def ad.calm_bg(+t: List<&2, Ad.Tk>, zi: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat}, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}) -> {AT.calm(Ad.mark(Ad.Bg{}, t)) == True{} : Bool}:
  +t2 = Ad.mark(Ad.Bg{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +wi2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +hb2 = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)
  %Equal.sym(Nat, wi2, wi, LAAdmissionBit.ad.cnt_mark(Ad.Waiting{}, Ad.Ia{}, t, Ad.Bg{}, nz)) : {AT.calm.n(_, hb2) == True{} : Bool}
  %Equal.sym(Nat, wi, 0n, zi) : {AT.calm.n(_, hb2) == True{} : Bool}
  LABool.ad.or_t(Ad.isz(hb2))

def ad.end_calm(+ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, +s: Ad.Sts, +e: {Ad.get(ts, k) == Some{Ad.Tk{c, s}} : Maybe<&2, Ad.Tk>}, cm: {AT.calm(ts) == True{} : Bool}) -> {AT.calm(Ad.put(ts, k, Ad.Ended{})) == True{} : Bool}:
  +t2 = Ad.put(ts, k, Ad.Ended{})
  +x = {Ad.Tk{c, s} : Ad.Tk}
  +x2 = Ad.hit(Ad.Waiting{}, Ad.Ia{}, x)
  +x3 = Ad.hit(Ad.Holding{}, Ad.Bg{}, x)
  +a2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +a3 = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)
  ad.calm_mono(x2, x3, a2, a3, ad.calm.tr(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), Ad.bit(x2, a2), Ad.bit(x3, a3), Equal.sym(Nat, Ad.bit(x2, a2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Waiting{}, Ad.Ia{}, ts, k, c, s, e)), Equal.sym(Nat, Ad.bit(x3, a3), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, s, e)), cm))

def ad.calm_of(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, h: {LALogic.ad.ok(l, ts) == True{} : Bool}) -> {AT.calm(ts) == True{} : Bool}:
  LALogic.ad.and_r(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick(l, ts))), AT.calm(ts), h)

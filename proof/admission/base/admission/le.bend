# eukhe: lemmas the proofs of area admission share: admission/le

import Base
import ../../../../bend/admission.bend as Ad
import ./bit.bend as LAAdmissionBit
import ../logic.bend as LALogic

def ad.le_refl(n: Nat) -> {Ad.le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ad.le_refl(p)

# the waiters bound the grants still to come
def ad.fuel_ia(+t: List<&2, Ad.Tk>, -f: Nat, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)) == False{} : Bool}, fuel: {Ad.le(Ad.waits(t), 1n+f) == True{} : Bool}) -> {Ad.le(Ad.waits(Ad.mark(Ad.Ia{}, t)), f) == True{} : Bool}:
  +t2 = Ad.mark(Ad.Ia{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)
  +wi2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +wb2 = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2)
  %Equal.sym(Nat, wb2, wb, LAAdmissionBit.ad.cnt_mark(Ad.Waiting{}, Ad.Bg{}, t, Ad.Ia{}, nz)) : {Ad.le(Nat.add(wi2, _), f) == True{} : Bool}
  %Equal.sym(Nat, 1n+wi2, wi, LAAdmissionBit.ad.cnt_mark(Ad.Waiting{}, Ad.Ia{}, t, Ad.Ia{}, nz)) : {Ad.le(Nat.add(_, wb), 1n+f) == True{} : Bool}
  fuel

def ad.fuel_bg(+t: List<&2, Ad.Tk>, -f: Nat, +zi: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat}, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}, fuel: {Ad.le(Ad.waits(t), 1n+f) == True{} : Bool}) -> {Ad.le(Ad.waits(Ad.mark(Ad.Bg{}, t)), f) == True{} : Bool}:
  +t2 = Ad.mark(Ad.Bg{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)
  +wi2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +wb2 = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2)
  %Equal.sym(Nat, wi2, wi, LAAdmissionBit.ad.cnt_mark(Ad.Waiting{}, Ad.Ia{}, t, Ad.Bg{}, nz)) : {Ad.le(Nat.add(_, wb2), f) == True{} : Bool}
  %Equal.sym(Nat, wi, 0n, zi) : {Ad.le(Nat.add(_, wb2), f) == True{} : Bool}
  %Equal.sym(Nat, 1n+wb2, wb, LAAdmissionBit.ad.cnt_mark(Ad.Waiting{}, Ad.Bg{}, t, Ad.Bg{}, nz)) : {Ad.le(_, 1n+f) == True{} : Bool}
  %zi : {Ad.le(Nat.add(_, wb), 1n+f) == True{} : Bool}
  fuel

# Slots held stay within the limit
# --------------------------------

def ad.le_trans(a: Nat, b: Nat, c: Nat, ab: {Ad.le(a, b) == True{} : Bool}, bc: {Ad.le(b, c) == True{} : Bool}) -> {Ad.le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      {==}
    case 1n+x 0n _:
      LALogic.ad.absurd({Ad.le(1n+x, c) == True{} : Bool}, ab)
    case 1n+x 1n+y 0n:
      LALogic.ad.absurd({Ad.le(1n+x, 0n) == True{} : Bool}, bc)
    case 1n+x 1n+y 1n+z:
      ad.le_trans(x, y, z, ab, bc)

# ---- admission_wait ----

# proof_admission_wait: the interactive bound of LAWS.bend (rule H3.4 of
# docs/harness.md). An interactive waiter w waits for ahead(s, w): the
# interactive slots held and the interactive waiters older than w. No op
# raises it, a release of an interactive slot lowers it by one, and
# while w waits it is at least one (no lost wake-up). So w is granted
# after at most ahead(s, w) interactive releases, whatever background
# requests do.

# Numbers
# -------

def aw.le_succ(x: Nat, +y: Nat, e: {Ad.le(x, y) == True{} : Bool}) -> {Ad.le(x, 1n+y) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+a:
      match y:
        case 0n:
          LALogic.ad.absurd({Ad.le(1n+a, 1n) == True{} : Bool}, e)
        case 1n+b:
          aw.le_succ(a, b, e)

def aw.bit_mono(b: Bool, -x: Nat, -y: Nat, e: {Ad.le(x, y) == True{} : Bool}) -> {Ad.le(Ad.bit(b, x), Ad.bit(b, y)) == True{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      e

def aw.bit_or(a: Bool, b: Bool, +y: Nat) -> {Ad.le(Ad.bit(a, y), Ad.bit(Bool.or(a, b), y)) == True{} : Bool}:
  match a b:
    case True{} _:
      ad.le_refl(y)
    case False{} True{}:
      aw.le_succ(y, y, ad.le_refl(y))
    case False{} False{}:
      ad.le_refl(y)

# One op
# ------

def aw.ia_new(-r: Bool, u: Bool, +p: Nat) -> {Ad.le(Ad.bit(Bool.and(Ad.Mode.of(Ad.Holding{}, Ad.admit.ia.st(Bool.and(False{}, r), u)), True{}), p), p) == True{} : Bool}:
  match u:
    case True{}:
      ad.le_refl(p)
    case False{}:
      ad.le_refl(p)

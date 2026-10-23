# eukhe: lemmas the proofs of area admission share: admission/cnt

import Base
import ../../../../bend/admission.bend as Ad
import ./bit.bend as LAAdmissionBit
import ../logic.bend as LALogic

def ad.bg_wi(-t: List<&2, Ad.Tk>, p: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool})) -> {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat}:
  (a, b, c) = p
  a

def ad.bg_hi(-t: List<&2, Ad.Tk>, p: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool})) -> {Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat}:
  (a, b, c) = p
  b

# a ticket appended counts last
def ad.cnt_app(+m: Ad.Mode, +c: Ad.Cls, t: List<&2, Ad.Tk>, +x: Ad.Tk) -> {Ad.cnt(m, c, List.append(&2, Ad.Tk, t, [x])) == Ad.bit(Ad.hit(m, c, x), Ad.cnt(m, c, t)) : Nat}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      %Equal.sym(Nat, Ad.cnt(m, c, List.append(&2, Ad.Tk, r, [x])), Ad.bit(Ad.hit(m, c, x), Ad.cnt(m, c, r)), ad.cnt_app(m, c, r, x)) : {Ad.bit(Ad.hit(m, c, h), _) == Ad.bit(Ad.hit(m, c, x), Ad.bit(Ad.hit(m, c, h), Ad.cnt(m, c, r))) : Nat}
      LAAdmissionBit.ad.bit_comm(Ad.hit(m, c, h), Ad.hit(m, c, x), Ad.cnt(m, c, r))

# a ticket appended that the count does not see
def ad.app_off(+m: Ad.Mode, +c: Ad.Cls, +t: List<&2, Ad.Tk>, +x: Ad.Tk, off: {Ad.hit(m, c, x) == False{} : Bool}) -> {Ad.cnt(m, c, List.append(&2, Ad.Tk, t, [x])) == Ad.cnt(m, c, t) : Nat}:
  Equal.trans(Nat, Ad.cnt(m, c, List.append(&2, Ad.Tk, t, [x])), Ad.bit(Ad.hit(m, c, x), Ad.cnt(m, c, t)), Ad.cnt(m, c, t), ad.cnt_app(m, c, t, x), LAAdmissionBit.ad.bit_off(Ad.hit(m, c, x), Ad.cnt(m, c, t), off))

# collecting a granted permit changes no count
def ad.col_cnt(m: Ad.Mode, +cc: Ad.Cls, +ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, e: {Ad.get(ts, k) == Some{Ad.Tk{c, Ad.Granted{}}} : Maybe<&2, Ad.Tk>}) -> {Ad.cnt(m, cc, Ad.put(ts, k, Ad.Held{})) == Ad.cnt(m, cc, ts) : Nat}:
  match m:
    case Ad.Holding{}:
      LALogic.ad.bit_inj(Ad.Cls.eq(cc, c), Ad.cnt(Ad.Holding{}, cc, Ad.put(ts, k, Ad.Held{})), Ad.cnt(Ad.Holding{}, cc, ts), LAAdmissionBit.ad.put_at(Ad.Holding{}, cc, ts, k, Ad.Held{}, Some{Ad.Tk{c, Ad.Granted{}}}, e))
    case Ad.Waiting{}:
      LAAdmissionBit.ad.put_at(Ad.Waiting{}, cc, ts, k, Ad.Held{}, Some{Ad.Tk{c, Ad.Granted{}}}, e)

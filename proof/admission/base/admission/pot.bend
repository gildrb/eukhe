# eukhe: lemmas the proofs of area admission share: admission/pot

import Base
import ../../../../bend/admission.bend as Ad
import ./bit.bend as LAAdmissionBit
import ./cnt.bend as LAAdmissionCnt
import ./get.bend as LAAdmissionGet
import ./hit.bend as LAAdmissionHit
import ./le.bend as LAAdmissionLe
import ../bool.bend as LABool
import ../logic.bend as LALogic
import ./terms.bend as AT
import ../../../../laws/admission.bend as Admission

# What w waits for
# ----------------

def aw.pot0(t: List<&2, Ad.Tk>) -> {AT.pot(t, 0n) == Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case h <> r:
      {==}

# What each change does to it
# ---------------------------

def aw.pot_pre(t: List<&2, Ad.Tk>, +w: Nat) -> {AT.pot(Ad.preempt(t), w) == AT.pot(t, w) : Nat}:
  match t w:
    case Nil{} _:
      {==}
    case +h <> +r 0n:
      LAAdmissionHit.ad.pre_ia(Ad.Holding{}, h <> r)
    case +h <> +r 1n+p:
      +hh = Ad.hit(Ad.Holding{}, Ad.Ia{}, h)
      +hw = Ad.hit(Ad.Waiting{}, Ad.Ia{}, h)
      +rhs = Ad.bit(Bool.or(hh, hw), AT.pot(r, p))
      %Equal.sym(Bool, Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk.preempt(h)), hh, LAAdmissionHit.ad.hit_pre(Ad.Holding{}, h)) : {Ad.bit(Bool.or(_, Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk.preempt(h))), AT.pot(Ad.preempt(r), p)) == rhs : Nat}
      %Equal.sym(Bool, Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk.preempt(h)), hw, LAAdmissionHit.ad.hit_pre(Ad.Waiting{}, h)) : {Ad.bit(Bool.or(hh, _), AT.pot(Ad.preempt(r), p)) == rhs : Nat}
      %Equal.sym(Nat, AT.pot(Ad.preempt(r), p), AT.pot(r, p), aw.pot_pre(r, p)) : {Ad.bit(Bool.or(hh, hw), _) == rhs : Nat}
      {==}

def aw.pot_pre_on(l: Ad.Lim, t: List<&2, Ad.Tk>, +w: Nat) -> {AT.pot(Ad.preempt.on(l, t), w) == AT.pot(t, w) : Nat}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      aw.pot_pre(t, w)

# a new ticket comes after w
def aw.pot_app(t: List<&2, Ad.Tk>, +x: Ad.Tk, +w: Nat, ws: {Admission.adm_waits_ia(Ad.get(t, w)) == True{} : Bool}) -> {AT.pot(List.append(&2, Ad.Tk, t, [x]), w) == Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), AT.pot(t, w)) : Nat}:
  match t w:
    case Nil{} _:
      LALogic.ad.absurd({AT.pot([x], w) == Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), 0n) : Nat}, ws)
    case +h <> +r 0n:
      LAAdmissionCnt.ad.cnt_app(Ad.Holding{}, Ad.Ia{}, h <> r, x)
    case +h <> +r 1n+p:
      +b = Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, h), Ad.hit(Ad.Waiting{}, Ad.Ia{}, h))
      +hx = Ad.hit(Ad.Holding{}, Ad.Ia{}, x)
      %Equal.sym(Nat, AT.pot(List.append(&2, Ad.Tk, r, [x]), p), Ad.bit(hx, AT.pot(r, p)), aw.pot_app(r, x, p, ws)) : {Ad.bit(b, _) == Ad.bit(hx, Ad.bit(b, AT.pot(r, p))) : Nat}
      LAAdmissionBit.ad.bit_comm(b, hx, AT.pot(r, p))

def aw.end0(+r: List<&2, Ad.Tk>, +q: Nat, -a: Bool, ih: {Ad.le(Ad.bit(a, AT.pot(Ad.put(r, q, Ad.Ended{}), 0n)), AT.pot(r, 0n)) == True{} : Bool}) -> {Ad.le(Ad.bit(a, Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(r, q, Ad.Ended{}))), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r)) == True{} : Bool}:
  %aw.pot0(Ad.put(r, q, Ad.Ended{})) : {Ad.le(Ad.bit(a, _), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r)) == True{} : Bool}
  %aw.pot0(r) : {Ad.le(Ad.bit(a, AT.pot(Ad.put(r, q, Ad.Ended{}), 0n)), _) == True{} : Bool}
  ih

# a ticket that ends drops what it weighed (an interactive slot at
# least, if it held one)
def aw.pot_end(t: List<&2, Ad.Tk>, +k: Nat, +w: Nat) -> {Ad.le(Ad.bit(LALogic.ad.at(Ad.Holding{}, Ad.Ia{}, Ad.get(t, k)), AT.pot(Ad.put(t, k, Ad.Ended{}), w)), AT.pot(t, w)) == True{} : Bool}:
  match t k w:
    case Nil{} _ _:
      {==}
    case Ad.Tk{+c1, +s1} <> +r 0n 0n:
      LAAdmissionLe.ad.le_refl(Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{c1, s1}), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r)))
    case Ad.Tk{+c1, +s1} <> +r 0n 1n+p:
      LAAdmissionLe.aw.bit_or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{c1, s1}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{c1, s1}), AT.pot(r, p))
    case Ad.Tk{+c1, +s1} <> +r 1n+q 0n:
      +hh = Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{c1, s1})
      +a = LALogic.ad.at(Ad.Holding{}, Ad.Ia{}, Ad.get(r, q))
      +x = Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(r, q, Ad.Ended{}))
      %LAAdmissionBit.ad.bit_comm(hh, a, x) : {Ad.le(_, Ad.bit(hh, Ad.cnt(Ad.Holding{}, Ad.Ia{}, r))) == True{} : Bool}
      LAAdmissionLe.aw.bit_mono(hh, Ad.bit(a, x), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.end0(r, q, a, aw.pot_end(r, q, 0n)))
    case Ad.Tk{+c1, +s1} <> +r 1n+q 1n+p:
      +a = LALogic.ad.at(Ad.Holding{}, Ad.Ia{}, Ad.get(r, q))
      +b = Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{c1, s1}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{c1, s1}))
      %LAAdmissionBit.ad.bit_comm(b, a, AT.pot(Ad.put(r, q, Ad.Ended{}), p)) : {Ad.le(_, Ad.bit(b, AT.pot(r, p))) == True{} : Bool}
      LAAdmissionLe.aw.bit_mono(b, Ad.bit(a, AT.pot(Ad.put(r, q, Ad.Ended{}), p)), AT.pot(r, p), aw.pot_end(r, q, p))

def aw.c_of(+x: List<&2, Ad.Tk>, +y: List<&2, Ad.Tk>, e: {AT.pot(x, 0n) == AT.pot(y, 0n) : Nat}) -> {Ad.cnt(Ad.Holding{}, Ad.Ia{}, x) == Ad.cnt(Ad.Holding{}, Ad.Ia{}, y) : Nat}:
  %aw.pot0(x) : {_ == Ad.cnt(Ad.Holding{}, Ad.Ia{}, y) : Nat}
  %aw.pot0(y) : {AT.pot(x, 0n) == _ : Nat}
  e

def aw.col0(+c1: Ad.Cls, s1: Ad.Sts, -r: List<&2, Ad.Tk>, w: Nat, g: {LALogic.ad.isg(Some{Ad.Tk{c1, s1}}) == True{} : Bool}) -> {AT.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) == AT.pot(Ad.Tk{c1, s1} <> r, w) : Nat}:
  match s1:
    case Ad.Granted{}:
      match w:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Ad.Queued{}:
      LALogic.ad.absurd({AT.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) == AT.pot(Ad.Tk{c1, Ad.Queued{}} <> r, w) : Nat}, g)
    case Ad.Held{}:
      LALogic.ad.absurd({AT.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) == AT.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) : Nat}, g)
    case Ad.Preempted{}:
      LALogic.ad.absurd({AT.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) == AT.pot(Ad.Tk{c1, Ad.Preempted{}} <> r, w) : Nat}, g)
    case Ad.Ended{}:
      LALogic.ad.absurd({AT.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) == AT.pot(Ad.Tk{c1, Ad.Ended{}} <> r, w) : Nat}, g)

# collecting a grant changes nothing w waits for
def aw.pot_col(t: List<&2, Ad.Tk>, +k: Nat, +w: Nat, +g: {LALogic.ad.isg(Ad.get(t, k)) == True{} : Bool}) -> {AT.pot(Ad.put(t, k, Ad.Held{}), w) == AT.pot(t, w) : Nat}:
  match t k w:
    case Nil{} _ _:
      {==}
    case Ad.Tk{+c1, +s1} <> +r 0n 0n:
      aw.col0(c1, s1, r, 0n, g)
    case Ad.Tk{+c1, +s1} <> +r 0n 1n+p:
      aw.col0(c1, s1, r, 1n+p, g)
    case Ad.Tk{+c1, +s1} <> +r 1n+q 0n:
      +hh = Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{c1, s1})
      Equal.cong(Nat, Nat, y => Ad.bit(hh, y), Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(r, q, Ad.Held{})), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.c_of(Ad.put(r, q, Ad.Held{}), r, aw.pot_col(r, q, 0n, g)))
    case Ad.Tk{+c1, +s1} <> +r 1n+q 1n+p:
      +b = Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{c1, s1}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{c1, s1}))
      Equal.cong(Nat, Nat, y => Ad.bit(b, y), AT.pot(Ad.put(r, q, Ad.Held{}), p), AT.pot(r, p), aw.pot_col(r, q, p, g))

# an interactive grant while w waits goes to a waiter ahead of it: it
# moves from waiting to holding, which w waits for alike
def aw.pot_mark_ia(t: List<&2, Ad.Tk>, +w: Nat, +e: {Admission.adm_waits_ia(Ad.get(Ad.mark(Ad.Ia{}, t), w)) == True{} : Bool}) -> {AT.pot(Ad.mark(Ad.Ia{}, t), w) == AT.pot(t, w) : Nat}:
  match t:
    case Nil{}:
      {==}
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs w:
        case Ad.Ia{} Ad.Queued{} 0n:
          LALogic.ad.absurd({AT.pot(Ad.Tk{Ad.Ia{}, Ad.Granted{}} <> r, 0n) == AT.pot(Ad.Tk{Ad.Ia{}, Ad.Queued{}} <> r, 0n) : Nat}, e)
        case Ad.Ia{} Ad.Queued{} 1n+p:
          {==}
        case Ad.Ia{} Ad.Granted{} 0n:
          LALogic.ad.absurd({AT.pot(Ad.Tk{Ad.Ia{}, Ad.Granted{}} <> Ad.mark(Ad.Ia{}, r), 0n) == AT.pot(Ad.Tk{Ad.Ia{}, Ad.Granted{}} <> r, 0n) : Nat}, e)
        case Ad.Ia{} Ad.Granted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Granted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Granted{}})), y), AT.pot(Ad.mark(Ad.Ia{}, r), p), AT.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Ia{} Ad.Held{} 0n:
          LALogic.ad.absurd({AT.pot(Ad.Tk{Ad.Ia{}, Ad.Held{}} <> Ad.mark(Ad.Ia{}, r), 0n) == AT.pot(Ad.Tk{Ad.Ia{}, Ad.Held{}} <> r, 0n) : Nat}, e)
        case Ad.Ia{} Ad.Held{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Held{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Held{}})), y), AT.pot(Ad.mark(Ad.Ia{}, r), p), AT.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Ia{} Ad.Preempted{} 0n:
          LALogic.ad.absurd({AT.pot(Ad.Tk{Ad.Ia{}, Ad.Preempted{}} <> Ad.mark(Ad.Ia{}, r), 0n) == AT.pot(Ad.Tk{Ad.Ia{}, Ad.Preempted{}} <> r, 0n) : Nat}, e)
        case Ad.Ia{} Ad.Preempted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Preempted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Preempted{}})), y), AT.pot(Ad.mark(Ad.Ia{}, r), p), AT.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Ia{} Ad.Ended{} 0n:
          LALogic.ad.absurd({AT.pot(Ad.Tk{Ad.Ia{}, Ad.Ended{}} <> Ad.mark(Ad.Ia{}, r), 0n) == AT.pot(Ad.Tk{Ad.Ia{}, Ad.Ended{}} <> r, 0n) : Nat}, e)
        case Ad.Ia{} Ad.Ended{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Ended{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Ended{}})), y), AT.pot(Ad.mark(Ad.Ia{}, r), p), AT.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Bg{} Ad.Queued{} 0n:
          LALogic.ad.absurd({AT.pot(Ad.Tk{Ad.Bg{}, Ad.Queued{}} <> Ad.mark(Ad.Ia{}, r), 0n) == AT.pot(Ad.Tk{Ad.Bg{}, Ad.Queued{}} <> r, 0n) : Nat}, e)
        case Ad.Bg{} Ad.Queued{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Queued{}})), y), AT.pot(Ad.mark(Ad.Ia{}, r), p), AT.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Bg{} Ad.Granted{} 0n:
          LALogic.ad.absurd({AT.pot(Ad.Tk{Ad.Bg{}, Ad.Granted{}} <> Ad.mark(Ad.Ia{}, r), 0n) == AT.pot(Ad.Tk{Ad.Bg{}, Ad.Granted{}} <> r, 0n) : Nat}, e)
        case Ad.Bg{} Ad.Granted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Granted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Granted{}})), y), AT.pot(Ad.mark(Ad.Ia{}, r), p), AT.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Bg{} Ad.Held{} 0n:
          LALogic.ad.absurd({AT.pot(Ad.Tk{Ad.Bg{}, Ad.Held{}} <> Ad.mark(Ad.Ia{}, r), 0n) == AT.pot(Ad.Tk{Ad.Bg{}, Ad.Held{}} <> r, 0n) : Nat}, e)
        case Ad.Bg{} Ad.Held{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Held{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Held{}})), y), AT.pot(Ad.mark(Ad.Ia{}, r), p), AT.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Bg{} Ad.Preempted{} 0n:
          LALogic.ad.absurd({AT.pot(Ad.Tk{Ad.Bg{}, Ad.Preempted{}} <> Ad.mark(Ad.Ia{}, r), 0n) == AT.pot(Ad.Tk{Ad.Bg{}, Ad.Preempted{}} <> r, 0n) : Nat}, e)
        case Ad.Bg{} Ad.Preempted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Preempted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Preempted{}})), y), AT.pot(Ad.mark(Ad.Ia{}, r), p), AT.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Bg{} Ad.Ended{} 0n:
          LALogic.ad.absurd({AT.pot(Ad.Tk{Ad.Bg{}, Ad.Ended{}} <> Ad.mark(Ad.Ia{}, r), 0n) == AT.pot(Ad.Tk{Ad.Bg{}, Ad.Ended{}} <> r, 0n) : Nat}, e)
        case Ad.Bg{} Ad.Ended{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Ended{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Ended{}})), y), AT.pot(Ad.mark(Ad.Ia{}, r), p), AT.pot(r, p), aw.pot_mark_ia(r, p, e))

# a background grant changes nothing w waits for
def aw.pot_mark_bg(t: List<&2, Ad.Tk>, +w: Nat) -> {AT.pot(Ad.mark(Ad.Bg{}, t), w) == AT.pot(t, w) : Nat}:
  match t:
    case Nil{}:
      {==}
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs w:
        case Ad.Bg{} Ad.Queued{} 0n:
          {==}
        case Ad.Bg{} Ad.Queued{} 1n+p:
          {==}
        case Ad.Ia{} Ad.Queued{} 0n:
          Equal.cong(Nat, Nat, y => Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}), y), Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.mark(Ad.Bg{}, r)), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.c_of(Ad.mark(Ad.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case Ad.Ia{} Ad.Queued{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Queued{}})), y), AT.pot(Ad.mark(Ad.Bg{}, r), p), AT.pot(r, p), aw.pot_mark_bg(r, p))
        case _ Ad.Granted{} 0n:
          Equal.cong(Nat, Nat, y => Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Granted{}}), y), Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.mark(Ad.Bg{}, r)), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.c_of(Ad.mark(Ad.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ Ad.Granted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Granted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Granted{}})), y), AT.pot(Ad.mark(Ad.Bg{}, r), p), AT.pot(r, p), aw.pot_mark_bg(r, p))
        case _ Ad.Held{} 0n:
          Equal.cong(Nat, Nat, y => Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Held{}}), y), Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.mark(Ad.Bg{}, r)), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.c_of(Ad.mark(Ad.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ Ad.Held{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Held{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Held{}})), y), AT.pot(Ad.mark(Ad.Bg{}, r), p), AT.pot(r, p), aw.pot_mark_bg(r, p))
        case _ Ad.Preempted{} 0n:
          Equal.cong(Nat, Nat, y => Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Preempted{}}), y), Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.mark(Ad.Bg{}, r)), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.c_of(Ad.mark(Ad.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ Ad.Preempted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Preempted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Preempted{}})), y), AT.pot(Ad.mark(Ad.Bg{}, r), p), AT.pot(r, p), aw.pot_mark_bg(r, p))
        case _ Ad.Ended{} 0n:
          Equal.cong(Nat, Nat, y => Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Ended{}}), y), Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.mark(Ad.Bg{}, r)), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.c_of(Ad.mark(Ad.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ Ad.Ended{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Ended{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Ended{}})), y), AT.pot(Ad.mark(Ad.Bg{}, r), p), AT.pot(r, p), aw.pot_mark_bg(r, p))

# a new background request changes nothing w waits for
def aw.st_bg(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, +w: Nat, ws: {Admission.adm_waits_ia(Ad.get(ts, w)) == True{} : Bool}) -> {Ad.le(AT.pot(Ad.admit.bg(l, ts), w), AT.pot(ts, w)) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
  +st = Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))
  +y = {Ad.Tk{Ad.Bg{}, st} : Ad.Tk}
  +p = AT.pot(ts, w)
  %Equal.sym(Nat, AT.pot(List.append(&2, Ad.Tk, ts, [y]), w), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, y), p), aw.pot_app(ts, y, w, ws)) : {Ad.le(_, p) == True{} : Bool}
  %Equal.sym(Bool, Bool.and(Ad.Mode.of(Ad.Holding{}, st), False{}), False{}, LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, st))) : {Ad.le(Ad.bit(_, p), p) == True{} : Bool}
  LAAdmissionLe.ad.le_refl(p)

def aw.end_at(+ts: List<&2, Ad.Tk>, +k: Nat, +w: Nat, -mb: Maybe<&2, Ad.Tk>, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}) -> {Ad.le(Ad.bit(LALogic.ad.at(Ad.Holding{}, Ad.Ia{}, mb), AT.pot(Ad.put(ts, k, Ad.Ended{}), w)), AT.pot(ts, w)) == True{} : Bool}:
  %ej : {Ad.le(Ad.bit(LALogic.ad.at(Ad.Holding{}, Ad.Ia{}, _), AT.pot(Ad.put(ts, k, Ad.Ended{}), w)), AT.pot(ts, w)) == True{} : Bool}
  aw.pot_end(ts, k, w)

def aw.col(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +w: Nat, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}) -> {Ad.le(AT.pot(Admission.adm_ts(Ad.collect.at(mb, l, q, ts, k)), w), AT.pot(ts, w)) == True{} : Bool}:
  match mb:
    case None{}:
      LAAdmissionLe.ad.le_refl(AT.pot(ts, w))
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      LAAdmissionLe.ad.le_refl(AT.pot(ts, w))
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      %Equal.sym(Nat, AT.pot(Ad.put(ts, k, Ad.Held{}), w), AT.pot(ts, w), aw.pot_col(ts, k, w, LAAdmissionGet.ad.isg_at(ts, k, Some{Ad.Tk{c, Ad.Granted{}}}, ej, {==}))) : {Ad.le(_, AT.pot(ts, w)) == True{} : Bool}
      LAAdmissionLe.ad.le_refl(AT.pot(ts, w))
    case Some{Ad.Tk{c, Ad.Held{}}}:
      LAAdmissionLe.ad.le_refl(AT.pot(ts, w))
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      LAAdmissionLe.ad.le_refl(AT.pot(ts, w))
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      LAAdmissionLe.ad.le_refl(AT.pot(ts, w))

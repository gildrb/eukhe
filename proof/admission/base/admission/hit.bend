# eukhe: lemmas the proofs of area admission share: admission/hit

import Base
import ../../../../bend/admission.bend as Ad
import ./cnt.bend as LAAdmissionCnt
import ../bool.bend as LABool

# A preemption
# ------------

# it keeps an interactive ticket's counts
def ad.hit_pre(+m: Ad.Mode, t: Ad.Tk) -> {Ad.hit(m, Ad.Ia{}, Ad.Tk.preempt(t)) == Ad.hit(m, Ad.Ia{}, t) : Bool}:
  match t:
    case Ad.Tk{Ad.Ia{}, s}:
      {==}
    case Ad.Tk{Ad.Bg{}, s}:
      match s:
        case Ad.Queued{}:
          {==}
        case Ad.Granted{}:
          LABool.ad.and_ff(Ad.Mode.of(m, Ad.Queued{}), Ad.Mode.of(m, Ad.Granted{}))
        case Ad.Held{}:
          LABool.ad.and_ff(Ad.Mode.of(m, Ad.Preempted{}), Ad.Mode.of(m, Ad.Held{}))
        case Ad.Preempted{}:
          {==}
        case Ad.Ended{}:
          {==}

def ad.pre_ia(+m: Ad.Mode, t: List<&2, Ad.Tk>) -> {Ad.cnt(m, Ad.Ia{}, Ad.preempt(t)) == Ad.cnt(m, Ad.Ia{}, t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      %Equal.sym(Bool, Ad.hit(m, Ad.Ia{}, Ad.Tk.preempt(h)), Ad.hit(m, Ad.Ia{}, h), ad.hit_pre(m, h)) : {Ad.bit(_, Ad.cnt(m, Ad.Ia{}, Ad.preempt(r))) == Ad.bit(Ad.hit(m, Ad.Ia{}, h), Ad.cnt(m, Ad.Ia{}, r)) : Nat}
      %Equal.sym(Nat, Ad.cnt(m, Ad.Ia{}, Ad.preempt(r)), Ad.cnt(m, Ad.Ia{}, r), ad.pre_ia(m, r)) : {Ad.bit(Ad.hit(m, Ad.Ia{}, h), _) == Ad.bit(Ad.hit(m, Ad.Ia{}, h), Ad.cnt(m, Ad.Ia{}, r)) : Nat}
      {==}

# it leaves no background slot held
def ad.hb_pre(t: Ad.Tk) -> {Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk.preempt(t)) == False{} : Bool}:
  match t:
    case Ad.Tk{Ad.Ia{}, s}:
      LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, s))
    case Ad.Tk{Ad.Bg{}, s}:
      match s:
        case Ad.Queued{}:
          {==}
        case Ad.Granted{}:
          {==}
        case Ad.Held{}:
          {==}
        case Ad.Preempted{}:
          {==}
        case Ad.Ended{}:
          {==}

def ad.pre_hb(t: List<&2, Ad.Tk>) -> {Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.preempt(t)) == 0n : Nat}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      %Equal.sym(Bool, Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk.preempt(h)), False{}, ad.hb_pre(h)) : {Ad.bit(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.preempt(r))) == 0n : Nat}
      ad.pre_hb(r)

# an interactive ticket appended after a preemption
def ad.app_pre(+m: Ad.Mode, +ts: List<&2, Ad.Tk>, +x: Ad.Tk) -> {Ad.cnt(m, Ad.Ia{}, List.append(&2, Ad.Tk, Ad.preempt(ts), [x])) == Ad.bit(Ad.hit(m, Ad.Ia{}, x), Ad.cnt(m, Ad.Ia{}, ts)) : Nat}:
  +hx = Ad.hit(m, Ad.Ia{}, x)
  Equal.trans(Nat, Ad.cnt(m, Ad.Ia{}, List.append(&2, Ad.Tk, Ad.preempt(ts), [x])), Ad.bit(hx, Ad.cnt(m, Ad.Ia{}, Ad.preempt(ts))), Ad.bit(hx, Ad.cnt(m, Ad.Ia{}, ts)), LAAdmissionCnt.ad.cnt_app(m, Ad.Ia{}, Ad.preempt(ts), x), Equal.cong(Nat, Nat, y => Ad.bit(hx, y), Ad.cnt(m, Ad.Ia{}, Ad.preempt(ts)), Ad.cnt(m, Ad.Ia{}, ts), ad.pre_ia(m, ts)))

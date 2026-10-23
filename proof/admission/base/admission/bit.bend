# eukhe: lemmas the proofs of area admission share: admission/bit

import Base
import ../../../../bend/admission.bend as Ad
import ../logic.bend as LALogic

# Counting
# --------

def ad.bit_comm(a: Bool, b: Bool, -x: Nat) -> {Ad.bit(a, Ad.bit(b, x)) == Ad.bit(b, Ad.bit(a, x)) : Nat}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a ticket's new status counts in its place
def ad.cnt_put(+m: Ad.Mode, +c: Ad.Cls, t: List<&2, Ad.Tk>, +k: Nat, +x: Ad.Sts) -> {Ad.bit(LALogic.ad.at(m, c, Ad.get(t, k)), Ad.cnt(m, c, Ad.put(t, k, x))) == Ad.bit(LALogic.ad.at(m, c, LALogic.ad.set(Ad.get(t, k), x)), Ad.cnt(m, c, t)) : Nat}:
  match t:
    case Nil{}:
      {==}
    case Ad.Tk{+c1, +s1} <> +r:
      match k:
        case 0n:
          ad.bit_comm(Ad.hit(m, c, Ad.Tk{c1, s1}), Ad.hit(m, c, Ad.Tk{c1, x}), Ad.cnt(m, c, r))
        case 1n+p:
          +ha = LALogic.ad.at(m, c, Ad.get(r, p))
          +hs = LALogic.ad.at(m, c, LALogic.ad.set(Ad.get(r, p), x))
          +hh = Ad.hit(m, c, Ad.Tk{c1, s1})
          %ad.bit_comm(hh, ha, Ad.cnt(m, c, Ad.put(r, p, x))) : {_ == Ad.bit(hs, Ad.bit(hh, Ad.cnt(m, c, r))) : Nat}
          %Equal.sym(Nat, Ad.bit(ha, Ad.cnt(m, c, Ad.put(r, p, x))), Ad.bit(hs, Ad.cnt(m, c, r)), ad.cnt_put(m, c, r, p, x)) : {Ad.bit(hh, _) == Ad.bit(hs, Ad.bit(hh, Ad.cnt(m, c, r))) : Nat}
          ad.bit_comm(hh, hs, Ad.cnt(m, c, r))

# A grant
# -------

# the grant passes a ticket that is not the oldest waiter of class c
def ad.mark_skip(+m: Ad.Mode, +d: Ad.Cls, +c: Ad.Cls, +h: Ad.Tk, +r: List<&2, Ad.Tk>, ih: {Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Queued{}}), Ad.cnt(m, d, Ad.mark(c, r))) == Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Granted{}}), Ad.cnt(m, d, r)) : Nat}) -> {Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Queued{}}), Ad.bit(Ad.hit(m, d, h), Ad.cnt(m, d, Ad.mark(c, r)))) == Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Granted{}}), Ad.bit(Ad.hit(m, d, h), Ad.cnt(m, d, r))) : Nat}:
  +hq = Ad.hit(m, d, Ad.Tk{c, Ad.Queued{}})
  +hg = Ad.hit(m, d, Ad.Tk{c, Ad.Granted{}})
  +hh = Ad.hit(m, d, h)
  %ad.bit_comm(hh, hq, Ad.cnt(m, d, Ad.mark(c, r))) : {_ == Ad.bit(hg, Ad.bit(hh, Ad.cnt(m, d, r))) : Nat}
  %Equal.sym(Nat, Ad.bit(hq, Ad.cnt(m, d, Ad.mark(c, r))), Ad.bit(hg, Ad.cnt(m, d, r)), ih) : {Ad.bit(hh, _) == Ad.bit(hg, Ad.bit(hh, Ad.cnt(m, d, r))) : Nat}
  ad.bit_comm(hh, hg, Ad.cnt(m, d, r))

# a grant to class c turns one waiter of c into a slot held
def ad.cnt_mark(+m: Ad.Mode, +d: Ad.Cls, t: List<&2, Ad.Tk>, +c: Ad.Cls, nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, c, t)) == False{} : Bool}) -> {Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Queued{}}), Ad.cnt(m, d, Ad.mark(c, t))) == Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Granted{}}), Ad.cnt(m, d, t)) : Nat}:
  match t:
    case Nil{}:
      LALogic.ad.absurd_t({Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Queued{}}), 0n) == Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Granted{}}), 0n) : Nat}, nz)
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs:
        case Ad.Ia{} Ad.Queued{}:
          match c:
            case Ad.Ia{}:
              ad.bit_comm(Ad.hit(m, d, Ad.Tk{Ad.Ia{}, Ad.Queued{}}), Ad.hit(m, d, Ad.Tk{Ad.Ia{}, Ad.Granted{}}), Ad.cnt(m, d, r))
            case Ad.Bg{}:
              ad.mark_skip(m, d, Ad.Bg{}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}, r, ad.cnt_mark(m, d, r, Ad.Bg{}, nz))
        case Ad.Bg{} Ad.Queued{}:
          match c:
            case Ad.Ia{}:
              ad.mark_skip(m, d, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}, r, ad.cnt_mark(m, d, r, Ad.Ia{}, nz))
            case Ad.Bg{}:
              ad.bit_comm(Ad.hit(m, d, Ad.Tk{Ad.Bg{}, Ad.Queued{}}), Ad.hit(m, d, Ad.Tk{Ad.Bg{}, Ad.Granted{}}), Ad.cnt(m, d, r))
        case _ Ad.Granted{}:
          ad.mark_skip(m, d, c, Ad.Tk{hc, Ad.Granted{}}, r, ad.cnt_mark(m, d, r, c, nz))
        case _ Ad.Held{}:
          ad.mark_skip(m, d, c, Ad.Tk{hc, Ad.Held{}}, r, ad.cnt_mark(m, d, r, c, nz))
        case _ Ad.Preempted{}:
          ad.mark_skip(m, d, c, Ad.Tk{hc, Ad.Preempted{}}, r, ad.cnt_mark(m, d, r, c, nz))
        case _ Ad.Ended{}:
          ad.mark_skip(m, d, c, Ad.Tk{hc, Ad.Ended{}}, r, ad.cnt_mark(m, d, r, c, nz))

# Every op keeps the invariant
# ----------------------------

def ad.bit_off(-b: Bool, -x: Nat, off: {b == False{} : Bool}) -> {Ad.bit(b, x) == x : Nat}:
  %Equal.sym(Bool, b, False{}, off) : {Ad.bit(_, x) == x : Nat}
  {==}

def ad.put_at(+m: Ad.Mode, +cc: Ad.Cls, +ts: List<&2, Ad.Tk>, +k: Nat, +x: Ad.Sts, -mb: Maybe<&2, Ad.Tk>, e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}) -> {Ad.bit(LALogic.ad.at(m, cc, mb), Ad.cnt(m, cc, Ad.put(ts, k, x))) == Ad.bit(LALogic.ad.at(m, cc, LALogic.ad.set(mb, x)), Ad.cnt(m, cc, ts)) : Nat}:
  %e : {Ad.bit(LALogic.ad.at(m, cc, _), Ad.cnt(m, cc, Ad.put(ts, k, x))) == Ad.bit(LALogic.ad.at(m, cc, LALogic.ad.set(_, x)), Ad.cnt(m, cc, ts)) : Nat}
  ad.cnt_put(m, cc, ts, k, x)

# ending ticket k drops it from its count
def ad.end_cnt(m: Ad.Mode, +cc: Ad.Cls, +ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, +s: Ad.Sts, e: {Ad.get(ts, k) == Some{Ad.Tk{c, s}} : Maybe<&2, Ad.Tk>}) -> {Ad.bit(Ad.hit(m, cc, Ad.Tk{c, s}), Ad.cnt(m, cc, Ad.put(ts, k, Ad.Ended{}))) == Ad.cnt(m, cc, ts) : Nat}:
  match m:
    case Ad.Holding{}:
      ad.put_at(Ad.Holding{}, cc, ts, k, Ad.Ended{}, Some{Ad.Tk{c, s}}, e)
    case Ad.Waiting{}:
      ad.put_at(Ad.Waiting{}, cc, ts, k, Ad.Ended{}, Some{Ad.Tk{c, s}}, e)

def ad.adm_ia1(+l: Ad.Lim, +hi: Nat, +w: Nat, +wb1: Nat, u: Bool, er: {Ad.room(l, Nat.add(hi, 0n)) == False{} : Bool}) -> {LALogic.ad.ok.n(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(False{}, u)}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(False{}, u)}), 1n+w), 0n, wb1) == True{} : Bool}:
  match u:
    case True{}:
      %Equal.sym(Bool, Ad.room(l, Nat.add(hi, 0n)), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 1n+w, hi, wb1))), Ad.calm.n(hi, 1n+w, 0n)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Ad.room(l, Nat.add(hi, 0n)), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 2n+w, hi, wb1))), Ad.calm.n(hi, 2n+w, 0n)) == True{} : Bool}
      {==}

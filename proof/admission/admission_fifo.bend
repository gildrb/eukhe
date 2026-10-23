# eukhe: the proof of LAW admission_fifo

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/misc.bend as LAAdmissionMisc
import ./base/bool.bend as LABool

# Grants within a class go oldest first
# -------------------------------------

def ad.or_f(x: Bool) -> {Bool.or(x, False{}) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def ad.or_nt(-x: Bool, -y: Bool, e: {x == False{} : Bool}) -> {Bool.or(Bool.not(x), y) == True{} : Bool}:
  %Equal.sym(Bool, x, False{}, e) : {Bool.or(Bool.not(_), y) == True{} : Bool}
  {==}

# with no waiter seen yet, every holder is in order
def ad.f_any(t: List<&2, Ad.Tk>, +c: Ad.Cls, b: Bool, e: {Ad.fifo(c, t, True{}) == True{} : Bool}) -> {Ad.fifo(c, t, b) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match b:
        case True{}:
          e
        case False{}:
          ad.f_any(r, c, Ad.hit(Ad.Waiting{}, c, h), LABool.ad.and_r(Bool.not(Ad.hit(Ad.Holding{}, c, h)), Ad.fifo(c, r, True{}), e))

def ad.f_weak(+r: List<&2, Ad.Tk>, +c: Ad.Cls, s: Bool, w: Bool, e: {Ad.fifo(c, r, Bool.or(s, w)) == True{} : Bool}) -> {Ad.fifo(c, r, s) == True{} : Bool}:
  match s:
    case True{}:
      e
    case False{}:
      match w:
        case True{}:
          ad.f_any(r, c, False{}, e)
        case False{}:
          e

def ad.f_pre_ia(t: List<&2, Ad.Tk>, +s: Bool) -> {Ad.fifo(Ad.Ia{}, Ad.preempt(t), s) == Ad.fifo(Ad.Ia{}, t, s) : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      +hh = Ad.hit(Ad.Holding{}, Ad.Ia{}, h)
      +hw = Ad.hit(Ad.Waiting{}, Ad.Ia{}, h)
      +rhs = Bool.and(Bool.not(Bool.and(s, hh)), Ad.fifo(Ad.Ia{}, r, Bool.or(s, hw)))
      %Equal.sym(Bool, Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk.preempt(h)), hh, LAAdmissionMisc.ad.hit_pre(Ad.Holding{}, h)) : {Bool.and(Bool.not(Bool.and(s, _)), Ad.fifo(Ad.Ia{}, Ad.preempt(r), Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk.preempt(h))))) == rhs : Bool}
      %Equal.sym(Bool, Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk.preempt(h)), hw, LAAdmissionMisc.ad.hit_pre(Ad.Waiting{}, h)) : {Bool.and(Bool.not(Bool.and(s, hh)), Ad.fifo(Ad.Ia{}, Ad.preempt(r), Bool.or(s, _))) == rhs : Bool}
      %Equal.sym(Bool, Ad.fifo(Ad.Ia{}, Ad.preempt(r), Bool.or(s, hw)), Ad.fifo(Ad.Ia{}, r, Bool.or(s, hw)), ad.f_pre_ia(r, Bool.or(s, hw))) : {Bool.and(Bool.not(Bool.and(s, hh)), _) == rhs : Bool}
      {==}

def ad.f_pre_bg(t: List<&2, Ad.Tk>, +s: Bool) -> {Ad.fifo(Ad.Bg{}, Ad.preempt(t), s) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      +rest = Ad.fifo(Ad.Bg{}, Ad.preempt(r), Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk.preempt(h))))
      %Equal.sym(Bool, Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk.preempt(h)), False{}, LAAdmissionMisc.ad.hb_pre(h)) : {Bool.and(Bool.not(Bool.and(s, _)), rest) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(s, False{}), False{}, LABool.ad.and_f(s)) : {Bool.and(Bool.not(_), rest) == True{} : Bool}
      ad.f_pre_bg(r, Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk.preempt(h))))

def ad.fapp0(s: Bool, x: Bool, ok: {Bool.or(Bool.not(x), Bool.and(Bool.not(s), True{})) == True{} : Bool}) -> {Bool.and(Bool.not(Bool.and(s, x)), True{}) == True{} : Bool}:
  match s x:
    case True{} True{}:
      LABool.ad.absurd({False{} == True{} : Bool}, ok)
    case True{} False{}:
      {==}
    case False{} _:
      {==}

def ad.fapp_ok(x: Bool, s: Bool, w: Bool, n: Nat, ok: {Bool.or(Bool.not(x), Bool.and(Bool.not(s), Ad.isz(Ad.bit(w, n)))) == True{} : Bool}) -> {Bool.or(Bool.not(x), Bool.and(Bool.not(Bool.or(s, w)), Ad.isz(n))) == True{} : Bool}:
  match x s w:
    case False{} _ _:
      {==}
    case True{} True{} _:
      LABool.ad.absurd({Bool.or(False{}, Bool.and(False{}, Ad.isz(n))) == True{} : Bool}, ok)
    case True{} False{} True{}:
      LABool.ad.absurd({Bool.or(False{}, Bool.and(False{}, Ad.isz(n))) == True{} : Bool}, ok)
    case True{} False{} False{}:
      ok

# a ticket appended keeps the order, if it takes no slot while an older
# one of its class waits
def ad.f_app(t: List<&2, Ad.Tk>, +c: Ad.Cls, +s: Bool, +x: Ad.Tk, +e: {Ad.fifo(c, t, s) == True{} : Bool}, ok: {Bool.or(Bool.not(Ad.hit(Ad.Holding{}, c, x)), Bool.and(Bool.not(s), Ad.isz(Ad.cnt(Ad.Waiting{}, c, t)))) == True{} : Bool}) -> {Ad.fifo(c, List.append(&2, Ad.Tk, t, [x]), s) == True{} : Bool}:
  match t:
    case Nil{}:
      ad.fapp0(s, Ad.hit(Ad.Holding{}, c, x), ok)
    case +h <> +r:
      +hh = Ad.hit(Ad.Holding{}, c, h)
      +hw = Ad.hit(Ad.Waiting{}, c, h)
      LABool.ad.and_t(Bool.not(Bool.and(s, hh)), Ad.fifo(c, List.append(&2, Ad.Tk, r, [x]), Bool.or(s, hw)), LABool.ad.and_l(Bool.not(Bool.and(s, hh)), Ad.fifo(c, r, Bool.or(s, hw)), e), ad.f_app(r, c, Bool.or(s, hw), x, LABool.ad.and_r(Bool.not(Bool.and(s, hh)), Ad.fifo(c, r, Bool.or(s, hw)), e), ad.fapp_ok(Ad.hit(Ad.Holding{}, c, x), s, hw, Ad.cnt(Ad.Waiting{}, c, r), ok)))

# a ticket that ends keeps the order
def ad.f_end(t: List<&2, Ad.Tk>, +c: Ad.Cls, +s: Bool, k: Nat, +e: {Ad.fifo(c, t, s) == True{} : Bool}) -> {Ad.fifo(c, Ad.put(t, k, Ad.Ended{}), s) == True{} : Bool}:
  match t k:
    case Nil{} _:
      e
    case Ad.Tk{+hc, +hs} <> +r 0n:
      +hh = Ad.hit(Ad.Holding{}, c, Ad.Tk{hc, hs})
      +hw = Ad.hit(Ad.Waiting{}, c, Ad.Tk{hc, hs})
      %Equal.sym(Bool, Bool.and(s, False{}), False{}, LABool.ad.and_f(s)) : {Bool.and(Bool.not(_), Ad.fifo(c, r, Bool.or(s, False{}))) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(s, False{}), s, ad.or_f(s)) : {Ad.fifo(c, r, _) == True{} : Bool}
      ad.f_weak(r, c, s, hw, LABool.ad.and_r(Bool.not(Bool.and(s, hh)), Ad.fifo(c, r, Bool.or(s, hw)), e))
    case Ad.Tk{+hc, +hs} <> +r 1n+p:
      +hh = Ad.hit(Ad.Holding{}, c, Ad.Tk{hc, hs})
      +hw = Ad.hit(Ad.Waiting{}, c, Ad.Tk{hc, hs})
      LABool.ad.and_t(Bool.not(Bool.and(s, hh)), Ad.fifo(c, Ad.put(r, p, Ad.Ended{}), Bool.or(s, hw)), LABool.ad.and_l(Bool.not(Bool.and(s, hh)), Ad.fifo(c, r, Bool.or(s, hw)), e), ad.f_end(r, c, Bool.or(s, hw), p, LABool.ad.and_r(Bool.not(Bool.and(s, hh)), Ad.fifo(c, r, Bool.or(s, hw)), e)))

def ad.fcol0(+hc: Ad.Cls, hs: Ad.Sts, +r: List<&2, Ad.Tk>, +c: Ad.Cls, +s: Bool, e: {Ad.fifo(c, Ad.Tk{hc, hs} <> r, s) == True{} : Bool}, g: {LABool.ad.isg(Some{Ad.Tk{hc, hs}}) == True{} : Bool}) -> {Ad.fifo(c, Ad.Tk{hc, Ad.Held{}} <> r, s) == True{} : Bool}:
  match hs:
    case Ad.Queued{}:
      LABool.ad.absurd({Ad.fifo(c, Ad.Tk{hc, Ad.Held{}} <> r, s) == True{} : Bool}, g)
    case Ad.Granted{}:
      e
    case Ad.Held{}:
      LABool.ad.absurd({Ad.fifo(c, Ad.Tk{hc, Ad.Held{}} <> r, s) == True{} : Bool}, g)
    case Ad.Preempted{}:
      LABool.ad.absurd({Ad.fifo(c, Ad.Tk{hc, Ad.Held{}} <> r, s) == True{} : Bool}, g)
    case Ad.Ended{}:
      LABool.ad.absurd({Ad.fifo(c, Ad.Tk{hc, Ad.Held{}} <> r, s) == True{} : Bool}, g)

# collecting a grant keeps the order
def ad.f_col(t: List<&2, Ad.Tk>, +c: Ad.Cls, +s: Bool, k: Nat, +e: {Ad.fifo(c, t, s) == True{} : Bool}, g: {LABool.ad.isg(Ad.get(t, k)) == True{} : Bool}) -> {Ad.fifo(c, Ad.put(t, k, Ad.Held{}), s) == True{} : Bool}:
  match t k:
    case Nil{} _:
      e
    case Ad.Tk{+hc, +hs} <> +r 0n:
      ad.fcol0(hc, hs, r, c, s, e, g)
    case Ad.Tk{+hc, +hs} <> +r 1n+p:
      +hh = Ad.hit(Ad.Holding{}, c, Ad.Tk{hc, hs})
      +hw = Ad.hit(Ad.Waiting{}, c, Ad.Tk{hc, hs})
      LABool.ad.and_t(Bool.not(Bool.and(s, hh)), Ad.fifo(c, Ad.put(r, p, Ad.Held{}), Bool.or(s, hw)), LABool.ad.and_l(Bool.not(Bool.and(s, hh)), Ad.fifo(c, r, Bool.or(s, hw)), e), ad.f_col(r, c, Bool.or(s, hw), p, LABool.ad.and_r(Bool.not(Bool.and(s, hh)), Ad.fifo(c, r, Bool.or(s, hw)), e), g))

# a grant to class c takes its oldest waiter
def ad.f_mark(t: List<&2, Ad.Tk>, +c: Ad.Cls, e: {Ad.fifo(c, t, False{}) == True{} : Bool}) -> {Ad.fifo(c, Ad.mark(c, t), False{}) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs:
        case Ad.Ia{} Ad.Queued{}:
          match c:
            case Ad.Ia{}:
              ad.f_any(r, Ad.Ia{}, False{}, e)
            case Ad.Bg{}:
              ad.f_mark(r, Ad.Bg{}, e)
        case Ad.Bg{} Ad.Queued{}:
          match c:
            case Ad.Ia{}:
              ad.f_mark(r, Ad.Ia{}, e)
            case Ad.Bg{}:
              ad.f_any(r, Ad.Bg{}, False{}, e)
        case _ Ad.Granted{}:
          ad.f_mark(r, c, e)
        case _ Ad.Held{}:
          ad.f_mark(r, c, e)
        case _ Ad.Preempted{}:
          ad.f_mark(r, c, e)
        case _ Ad.Ended{}:
          ad.f_mark(r, c, e)

# a grant to the other class keeps the order: (c, d) is (Ia, Bg) or
# (Bg, Ia)
def ad.f_tail(+c: Ad.Cls, +h: Ad.Tk, -r: List<&2, Ad.Tk>, +s: Bool, e: {Ad.fifo(c, h <> r, s) == True{} : Bool}) -> {Ad.fifo(c, r, Bool.or(s, Ad.hit(Ad.Waiting{}, c, h))) == True{} : Bool}:
  LABool.ad.and_r(Bool.not(Bool.and(s, Ad.hit(Ad.Holding{}, c, h))), Ad.fifo(c, r, Bool.or(s, Ad.hit(Ad.Waiting{}, c, h))), e)

def ad.f_skip(+c: Ad.Cls, +h: Ad.Tk, -r2: List<&2, Ad.Tk>, -r: List<&2, Ad.Tk>, +s: Bool, e: {Ad.fifo(c, h <> r, s) == True{} : Bool}, ih: {Ad.fifo(c, r2, Bool.or(s, Ad.hit(Ad.Waiting{}, c, h))) == True{} : Bool}) -> {Ad.fifo(c, h <> r2, s) == True{} : Bool}:
  LABool.ad.and_t(Bool.not(Bool.and(s, Ad.hit(Ad.Holding{}, c, h))), Ad.fifo(c, r2, Bool.or(s, Ad.hit(Ad.Waiting{}, c, h))), LABool.ad.and_l(Bool.not(Bool.and(s, Ad.hit(Ad.Holding{}, c, h))), Ad.fifo(c, r, Bool.or(s, Ad.hit(Ad.Waiting{}, c, h))), e), ih)

def ad.f_mark_ib(t: List<&2, Ad.Tk>, +s: Bool, +e: {Ad.fifo(Ad.Ia{}, t, s) == True{} : Bool}) -> {Ad.fifo(Ad.Ia{}, Ad.mark(Ad.Bg{}, t), s) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs:
        case Ad.Bg{} Ad.Queued{}:
          e
        case Ad.Ia{} Ad.Queued{}:
          ad.f_skip(Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}, Ad.mark(Ad.Bg{}, r), r, s, e, ad.f_mark_ib(r, Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Queued{}})), ad.f_tail(Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}, r, s, e)))
        case _ Ad.Granted{}:
          ad.f_skip(Ad.Ia{}, Ad.Tk{hc, Ad.Granted{}}, Ad.mark(Ad.Bg{}, r), r, s, e, ad.f_mark_ib(r, Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Granted{}})), ad.f_tail(Ad.Ia{}, Ad.Tk{hc, Ad.Granted{}}, r, s, e)))
        case _ Ad.Held{}:
          ad.f_skip(Ad.Ia{}, Ad.Tk{hc, Ad.Held{}}, Ad.mark(Ad.Bg{}, r), r, s, e, ad.f_mark_ib(r, Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Held{}})), ad.f_tail(Ad.Ia{}, Ad.Tk{hc, Ad.Held{}}, r, s, e)))
        case _ Ad.Preempted{}:
          ad.f_skip(Ad.Ia{}, Ad.Tk{hc, Ad.Preempted{}}, Ad.mark(Ad.Bg{}, r), r, s, e, ad.f_mark_ib(r, Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Preempted{}})), ad.f_tail(Ad.Ia{}, Ad.Tk{hc, Ad.Preempted{}}, r, s, e)))
        case _ Ad.Ended{}:
          ad.f_skip(Ad.Ia{}, Ad.Tk{hc, Ad.Ended{}}, Ad.mark(Ad.Bg{}, r), r, s, e, ad.f_mark_ib(r, Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Ended{}})), ad.f_tail(Ad.Ia{}, Ad.Tk{hc, Ad.Ended{}}, r, s, e)))

def ad.f_mark_bi(t: List<&2, Ad.Tk>, +s: Bool, +e: {Ad.fifo(Ad.Bg{}, t, s) == True{} : Bool}) -> {Ad.fifo(Ad.Bg{}, Ad.mark(Ad.Ia{}, t), s) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs:
        case Ad.Ia{} Ad.Queued{}:
          e
        case Ad.Bg{} Ad.Queued{}:
          ad.f_skip(Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}, Ad.mark(Ad.Ia{}, r), r, s, e, ad.f_mark_bi(r, Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.Queued{}})), ad.f_tail(Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}, r, s, e)))
        case _ Ad.Granted{}:
          ad.f_skip(Ad.Bg{}, Ad.Tk{hc, Ad.Granted{}}, Ad.mark(Ad.Ia{}, r), r, s, e, ad.f_mark_bi(r, Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk{hc, Ad.Granted{}})), ad.f_tail(Ad.Bg{}, Ad.Tk{hc, Ad.Granted{}}, r, s, e)))
        case _ Ad.Held{}:
          ad.f_skip(Ad.Bg{}, Ad.Tk{hc, Ad.Held{}}, Ad.mark(Ad.Ia{}, r), r, s, e, ad.f_mark_bi(r, Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk{hc, Ad.Held{}})), ad.f_tail(Ad.Bg{}, Ad.Tk{hc, Ad.Held{}}, r, s, e)))
        case _ Ad.Preempted{}:
          ad.f_skip(Ad.Bg{}, Ad.Tk{hc, Ad.Preempted{}}, Ad.mark(Ad.Ia{}, r), r, s, e, ad.f_mark_bi(r, Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk{hc, Ad.Preempted{}})), ad.f_tail(Ad.Bg{}, Ad.Tk{hc, Ad.Preempted{}}, r, s, e)))
        case _ Ad.Ended{}:
          ad.f_skip(Ad.Bg{}, Ad.Tk{hc, Ad.Ended{}}, Ad.mark(Ad.Ia{}, r), r, s, e, ad.f_mark_bi(r, Bool.or(s, Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk{hc, Ad.Ended{}})), ad.f_tail(Ad.Bg{}, Ad.Tk{hc, Ad.Ended{}}, r, s, e)))

def ad.f_grant(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +e: {Ad.fifo.both(t) == True{} : Bool}) -> {Ad.fifo.both(Ad.grant.go(n, d, l, t)) == True{} : Bool}:
  match n d:
    case 0n _:
      e
    case 1n+f None{}:
      e
    case 1n+f Some{Ad.Ia{}}:
      +t2 = Ad.mark(Ad.Ia{}, t)
      ad.f_grant(f, Ad.pick(l, t2), l, t2, LABool.ad.and_t(Ad.fifo(Ad.Ia{}, t2, False{}), Ad.fifo(Ad.Bg{}, t2, False{}), ad.f_mark(t, Ad.Ia{}, LABool.ad.and_l(Ad.fifo(Ad.Ia{}, t, False{}), Ad.fifo(Ad.Bg{}, t, False{}), e)), ad.f_mark_bi(t, False{}, LABool.ad.and_r(Ad.fifo(Ad.Ia{}, t, False{}), Ad.fifo(Ad.Bg{}, t, False{}), e))))
    case 1n+f Some{Ad.Bg{}}:
      +t2 = Ad.mark(Ad.Bg{}, t)
      ad.f_grant(f, Ad.pick(l, t2), l, t2, LABool.ad.and_t(Ad.fifo(Ad.Ia{}, t2, False{}), Ad.fifo(Ad.Bg{}, t2, False{}), ad.f_mark_ib(t, False{}, LABool.ad.and_l(Ad.fifo(Ad.Ia{}, t, False{}), Ad.fifo(Ad.Bg{}, t, False{}), e)), ad.f_mark(t, Ad.Bg{}, LABool.ad.and_r(Ad.fifo(Ad.Ia{}, t, False{}), Ad.fifo(Ad.Bg{}, t, False{}), e))))

def ad.f_end2(+ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.fifo.both(ts) == True{} : Bool}) -> {Ad.fifo.both(Ad.put(ts, k, Ad.Ended{})) == True{} : Bool}:
  +t2 = Ad.put(ts, k, Ad.Ended{})
  LABool.ad.and_t(Ad.fifo(Ad.Ia{}, t2, False{}), Ad.fifo(Ad.Bg{}, t2, False{}), ad.f_end(ts, Ad.Ia{}, False{}, k, LABool.ad.and_l(Ad.fifo(Ad.Ia{}, ts, False{}), Ad.fifo(Ad.Bg{}, ts, False{}), e)), ad.f_end(ts, Ad.Bg{}, False{}, k, LABool.ad.and_r(Ad.fifo(Ad.Ia{}, ts, False{}), Ad.fifo(Ad.Bg{}, ts, False{}), e)))

def ad.f_end_grant(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.fifo.both(ts) == True{} : Bool}) -> {Ad.fifo.both(Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))) == True{} : Bool}:
  +t2 = Ad.put(ts, k, Ad.Ended{})
  ad.f_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, ad.f_end2(ts, k, e))

def ad.f_col_op(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, +e: {Ad.fifo.both(ts) == True{} : Bool}) -> {Ad.fifo.both(Ad.St.ts(Ad.collect.at(mb, l, q, ts, k))) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      e
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      +t2 = Ad.put(ts, k, Ad.Held{})
      +g = LAAdmissionMisc.ad.isg_at(ts, k, Some{Ad.Tk{c, Ad.Granted{}}}, ej, {==})
      LABool.ad.and_t(Ad.fifo(Ad.Ia{}, t2, False{}), Ad.fifo(Ad.Bg{}, t2, False{}), ad.f_col(ts, Ad.Ia{}, False{}, k, LABool.ad.and_l(Ad.fifo(Ad.Ia{}, ts, False{}), Ad.fifo(Ad.Bg{}, ts, False{}), e), g), ad.f_col(ts, Ad.Bg{}, False{}, k, LABool.ad.and_r(Ad.fifo(Ad.Ia{}, ts, False{}), Ad.fifo(Ad.Bg{}, ts, False{}), e), g))
    case Some{Ad.Tk{c, Ad.Held{}}}:
      e
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      e
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      e

def ad.f_rel_op(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.fifo.both(ts) == True{} : Bool}) -> {Ad.fifo.both(Ad.St.ts(Ad.release.at(mb, l, q, ts, k))) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      e
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      e
    case Some{Ad.Tk{c, Ad.Held{}}}:
      ad.f_end_grant(l, ts, k, e)
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      ad.f_end2(ts, k, e)
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      e

def ad.f_lea_op(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.fifo.both(ts) == True{} : Bool}) -> {Ad.fifo.both(Ad.St.ts(Ad.leave.at(mb, l, q, ts, k))) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      ad.f_end_grant(l, ts, k, e)
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      ad.f_end_grant(l, ts, k, e)
    case Some{Ad.Tk{c, Ad.Held{}}}:
      e
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      e
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      e

def ad.fifo_ia_ok(wi: Nat, r: Bool, u: Bool) -> {Bool.or(Bool.not(Bool.and(Ad.Mode.of(Ad.Holding{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), r), u)), True{})), Ad.isz(wi)) == True{} : Bool}:
  match wi:
    case 0n:
      LABool.ad.or_t(Bool.not(Bool.and(Ad.Mode.of(Ad.Holding{}, Ad.admit.ia.st(r, u)), True{})))
    case 1n+w:
      match u:
        case True{}:
          {==}
        case False{}:
          {==}

def ad.fifo_bg_ok(a: Bool, b: Bool, w: Bool, r: Bool) -> {Bool.or(Bool.not(Bool.and(Ad.Mode.of(Ad.Holding{}, Ad.admit.bg.st(Bool.and(a, Bool.and(b, Bool.and(w, r))))), True{})), w) == True{} : Bool}:
  match a b w:
    case False{} _ _:
      {==}
    case True{} False{} _:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      LABool.ad.or_t(Bool.not(Bool.and(Ad.Mode.of(Ad.Holding{}, Ad.admit.bg.st(r)), True{})))

def ad.fifo_wi(-a: Nat, -b: Nat, -x: Bool, e: {b == a : Nat}, h: {Bool.or(x, Ad.isz(b)) == True{} : Bool}) -> {Bool.or(x, Bool.and(Bool.not(False{}), Ad.isz(a))) == True{} : Bool}:
  %e : {Bool.or(x, Ad.isz(_)) == True{} : Bool}
  h

def ad.f_step(s: Ad.St, o: Ad.Op, +e: {Ad.fifo.both(Ad.St.ts(s)) == True{} : Bool}) -> {Ad.fifo.both(Ad.St.ts(Ad.step(s, o))) == True{} : Bool}:
  match s o:
    case Ad.St{+l, +q, +ts} Ad.Admit{Ad.Ia{}}:
      +ei = LABool.ad.and_l(Ad.fifo(Ad.Ia{}, ts, False{}), Ad.fifo(Ad.Bg{}, ts, False{}), e)
      +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
      +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
      +st = Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))
      +x = {Ad.Tk{Ad.Ia{}, st} : Ad.Tk}
      +t1 = Ad.preempt(ts)
      +t2 = List.append(&2, Ad.Tk, t1, [x])
      +oki = ad.fifo_wi(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t1), wi, Bool.not(Ad.hit(Ad.Holding{}, Ad.Ia{}, x)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t1), wi, LAAdmissionMisc.ad.pre_ia(Ad.Waiting{}, ts)), ad.fifo_ia_ok(wi, Ad.room(l, hi), Ad.le(q, wi)))
      LABool.ad.and_t(Ad.fifo(Ad.Ia{}, t2, False{}), Ad.fifo(Ad.Bg{}, t2, False{}), ad.f_app(t1, Ad.Ia{}, False{}, x, Equal.trans(Bool, Ad.fifo(Ad.Ia{}, t1, False{}), Ad.fifo(Ad.Ia{}, ts, False{}), True{}, ad.f_pre_ia(ts, False{}), ei), oki), ad.f_app(t1, Ad.Bg{}, False{}, x, ad.f_pre_bg(ts, False{}), ad.or_nt(Ad.hit(Ad.Holding{}, Ad.Bg{}, x), Bool.and(True{}, Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1))), LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, st)))))
    case Ad.St{+l, +q, +ts} Ad.Admit{Ad.Bg{}}:
      +ei = LABool.ad.and_l(Ad.fifo(Ad.Ia{}, ts, False{}), Ad.fifo(Ad.Bg{}, ts, False{}), e)
      +eb = LABool.ad.and_r(Ad.fifo(Ad.Ia{}, ts, False{}), Ad.fifo(Ad.Bg{}, ts, False{}), e)
      +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
      +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
      +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
      +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
      +st = Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))
      +y = {Ad.Tk{Ad.Bg{}, st} : Ad.Tk}
      +t2 = List.append(&2, Ad.Tk, ts, [y])
      LABool.ad.and_t(Ad.fifo(Ad.Ia{}, t2, False{}), Ad.fifo(Ad.Bg{}, t2, False{}), ad.f_app(ts, Ad.Ia{}, False{}, y, ei, ad.or_nt(Ad.hit(Ad.Holding{}, Ad.Ia{}, y), Bool.and(True{}, Ad.isz(wi)), LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, st)))), ad.f_app(ts, Ad.Bg{}, False{}, y, eb, ad.fifo_bg_ok(Ad.isz(hi), Ad.isz(wi), Ad.isz(wb), Ad.room(l, Nat.add(hi, hb)))))
    case Ad.St{+l, +q, +ts} Ad.Collect{+k}:
      ad.f_col_op(Ad.get(ts, k), l, q, ts, k, {==}, e)
    case Ad.St{+l, +q, +ts} Ad.Release{+k}:
      ad.f_rel_op(Ad.get(ts, k), l, q, ts, k, e)
    case Ad.St{+l, +q, +ts} Ad.Leave{+k}:
      ad.f_lea_op(Ad.get(ts, k), l, q, ts, k, e)
    case Ad.St{+l, +q, +ts} Ad.Limit{+l2, q2}:
      ad.f_grant(Ad.waits(ts), Ad.pick(l2, ts), l2, ts, e)

def ad.run_fifo(os: List<&2, Ad.Op>, +s: Ad.St, e: {Ad.fifo.both(Ad.St.ts(s)) == True{} : Bool}) -> {Ad.fifo.both(Ad.St.ts(Ad.run(os, s))) == True{} : Bool}:
  match os:
    case Nil{}:
      e
    case +o <> r:
      ad.run_fifo(r, Ad.step(s, o), ad.f_step(s, o, e))

def fifo_per_class(+l: Ad.Lim, +q: Nat, +os: List<&2, Ad.Op>) -> {Ad.fifo.both(Ad.St.ts(Ad.run(os, Ad.St.new(l, q)))) == True{} : Bool}:
  ad.run_fifo(os, Ad.St.new(l, q), {==})

def Admission.admission_fifo(l, q, os):
  fifo_per_class(l, q, os)

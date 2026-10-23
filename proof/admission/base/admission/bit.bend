# eukhe: lemmas the proofs of area admission share: admission/bit

import Base
import ../../../../bend/admission.bend as Ad
import ./misc.bend as LAAdmissionMisc
import ../bool.bend as LABool
import ../maybe.bend as LAMaybe
import ../nat.bend as LANat

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

# a ticket appended counts last
def ad.cnt_app(+m: Ad.Mode, +c: Ad.Cls, t: List<&2, Ad.Tk>, +x: Ad.Tk) -> {Ad.cnt(m, c, List.append(&2, Ad.Tk, t, [x])) == Ad.bit(Ad.hit(m, c, x), Ad.cnt(m, c, t)) : Nat}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      %Equal.sym(Nat, Ad.cnt(m, c, List.append(&2, Ad.Tk, r, [x])), Ad.bit(Ad.hit(m, c, x), Ad.cnt(m, c, r)), ad.cnt_app(m, c, r, x)) : {Ad.bit(Ad.hit(m, c, h), _) == Ad.bit(Ad.hit(m, c, x), Ad.bit(Ad.hit(m, c, h), Ad.cnt(m, c, r))) : Nat}
      ad.bit_comm(Ad.hit(m, c, h), Ad.hit(m, c, x), Ad.cnt(m, c, r))

# a ticket's new status counts in its place
def ad.cnt_put(+m: Ad.Mode, +c: Ad.Cls, t: List<&2, Ad.Tk>, +k: Nat, +x: Ad.Sts) -> {Ad.bit(LABool.ad.at(m, c, Ad.get(t, k)), Ad.cnt(m, c, Ad.put(t, k, x))) == Ad.bit(LABool.ad.at(m, c, LAMaybe.ad.set(Ad.get(t, k), x)), Ad.cnt(m, c, t)) : Nat}:
  match t:
    case Nil{}:
      {==}
    case Ad.Tk{+c1, +s1} <> +r:
      match k:
        case 0n:
          ad.bit_comm(Ad.hit(m, c, Ad.Tk{c1, s1}), Ad.hit(m, c, Ad.Tk{c1, x}), Ad.cnt(m, c, r))
        case 1n+p:
          +ha = LABool.ad.at(m, c, Ad.get(r, p))
          +hs = LABool.ad.at(m, c, LAMaybe.ad.set(Ad.get(r, p), x))
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
      LABool.ad.absurd_t({Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Queued{}}), 0n) == Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Granted{}}), 0n) : Nat}, nz)
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

def ad.bit_inj(b: Bool, -x: Nat, -y: Nat, e: {Ad.bit(b, x) == Ad.bit(b, y) : Nat}) -> {x == y : Nat}:
  match b:
    case False{}:
      e
    case True{}:
      Equal.cong(Nat, Nat, n => LANat.ad.pred(n), 1n+x, 1n+y, e)

# Every op keeps the invariant
# ----------------------------

def ad.bit_off(-b: Bool, -x: Nat, off: {b == False{} : Bool}) -> {Ad.bit(b, x) == x : Nat}:
  %Equal.sym(Bool, b, False{}, off) : {Ad.bit(_, x) == x : Nat}
  {==}

# a ticket appended that the count does not see
def ad.app_off(+m: Ad.Mode, +c: Ad.Cls, +t: List<&2, Ad.Tk>, +x: Ad.Tk, off: {Ad.hit(m, c, x) == False{} : Bool}) -> {Ad.cnt(m, c, List.append(&2, Ad.Tk, t, [x])) == Ad.cnt(m, c, t) : Nat}:
  Equal.trans(Nat, Ad.cnt(m, c, List.append(&2, Ad.Tk, t, [x])), Ad.bit(Ad.hit(m, c, x), Ad.cnt(m, c, t)), Ad.cnt(m, c, t), ad.cnt_app(m, c, t, x), ad.bit_off(Ad.hit(m, c, x), Ad.cnt(m, c, t), off))

# an interactive ticket appended after a preemption
def ad.app_pre(+m: Ad.Mode, +ts: List<&2, Ad.Tk>, +x: Ad.Tk) -> {Ad.cnt(m, Ad.Ia{}, List.append(&2, Ad.Tk, Ad.preempt(ts), [x])) == Ad.bit(Ad.hit(m, Ad.Ia{}, x), Ad.cnt(m, Ad.Ia{}, ts)) : Nat}:
  +hx = Ad.hit(m, Ad.Ia{}, x)
  Equal.trans(Nat, Ad.cnt(m, Ad.Ia{}, List.append(&2, Ad.Tk, Ad.preempt(ts), [x])), Ad.bit(hx, Ad.cnt(m, Ad.Ia{}, Ad.preempt(ts))), Ad.bit(hx, Ad.cnt(m, Ad.Ia{}, ts)), ad.cnt_app(m, Ad.Ia{}, Ad.preempt(ts), x), Equal.cong(Nat, Nat, y => Ad.bit(hx, y), Ad.cnt(m, Ad.Ia{}, Ad.preempt(ts)), Ad.cnt(m, Ad.Ia{}, ts), LAAdmissionMisc.ad.pre_ia(m, ts)))

def ad.put_at(+m: Ad.Mode, +cc: Ad.Cls, +ts: List<&2, Ad.Tk>, +k: Nat, +x: Ad.Sts, -mb: Maybe<&2, Ad.Tk>, e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}) -> {Ad.bit(LABool.ad.at(m, cc, mb), Ad.cnt(m, cc, Ad.put(ts, k, x))) == Ad.bit(LABool.ad.at(m, cc, LAMaybe.ad.set(mb, x)), Ad.cnt(m, cc, ts)) : Nat}:
  %e : {Ad.bit(LABool.ad.at(m, cc, _), Ad.cnt(m, cc, Ad.put(ts, k, x))) == Ad.bit(LABool.ad.at(m, cc, LAMaybe.ad.set(_, x)), Ad.cnt(m, cc, ts)) : Nat}
  ad.cnt_put(m, cc, ts, k, x)

# collecting a granted permit changes no count
def ad.col_cnt(m: Ad.Mode, +cc: Ad.Cls, +ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, e: {Ad.get(ts, k) == Some{Ad.Tk{c, Ad.Granted{}}} : Maybe<&2, Ad.Tk>}) -> {Ad.cnt(m, cc, Ad.put(ts, k, Ad.Held{})) == Ad.cnt(m, cc, ts) : Nat}:
  match m:
    case Ad.Holding{}:
      ad.bit_inj(Ad.Cls.eq(cc, c), Ad.cnt(Ad.Holding{}, cc, Ad.put(ts, k, Ad.Held{})), Ad.cnt(Ad.Holding{}, cc, ts), ad.put_at(Ad.Holding{}, cc, ts, k, Ad.Held{}, Some{Ad.Tk{c, Ad.Granted{}}}, e))
    case Ad.Waiting{}:
      ad.put_at(Ad.Waiting{}, cc, ts, k, Ad.Held{}, Some{Ad.Tk{c, Ad.Granted{}}}, e)

# ending ticket k drops it from its count
def ad.end_cnt(m: Ad.Mode, +cc: Ad.Cls, +ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, +s: Ad.Sts, e: {Ad.get(ts, k) == Some{Ad.Tk{c, s}} : Maybe<&2, Ad.Tk>}) -> {Ad.bit(Ad.hit(m, cc, Ad.Tk{c, s}), Ad.cnt(m, cc, Ad.put(ts, k, Ad.Ended{}))) == Ad.cnt(m, cc, ts) : Nat}:
  match m:
    case Ad.Holding{}:
      ad.put_at(Ad.Holding{}, cc, ts, k, Ad.Ended{}, Some{Ad.Tk{c, s}}, e)
    case Ad.Waiting{}:
      ad.put_at(Ad.Waiting{}, cc, ts, k, Ad.Ended{}, Some{Ad.Tk{c, s}}, e)

# an interactive admit: after the preemption a slot goes to it only
# while no interactive request waits; else no slot is free
def ad.adm_ia0(+l: Ad.Lim, +hi: Nat, +wb1: Nat, r: Bool, u: Bool, er: {Ad.room(l, hi) == r : Bool}) -> {LABool.ad.ok.n(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(r, u)}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(r, u)}), 0n), 0n, wb1) == True{} : Bool}:
  match r u:
    case True{} _:
      +rr = Ad.room(l, Nat.add(1n+hi, 0n))
      %Equal.sym(Maybe<&2, Ad.Cls>, Ad.pick.go(rr, 0n, 1n+hi, wb1), None{}, LAAdmissionMisc.ad.pick_none_hi(rr, hi, wb1)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(1n+hi, 0n, 0n)) == True{} : Bool}
      {==}
    case False{} True{}:
      %Equal.sym(Nat, Nat.add(hi, 0n), hi, LANat.ad.add_zero(hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, _), 0n, hi, wb1))), Ad.calm.n(hi, 0n, 0n)) == True{} : Bool}
      %Equal.sym(Bool, Ad.room(l, hi), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 0n, hi, wb1))), Ad.calm.n(hi, 0n, 0n)) == True{} : Bool}
      {==}
    case False{} False{}:
      %Equal.sym(Nat, Nat.add(hi, 0n), hi, LANat.ad.add_zero(hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, _), 1n, hi, wb1))), Ad.calm.n(hi, 1n, 0n)) == True{} : Bool}
      %Equal.sym(Bool, Ad.room(l, hi), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 1n, hi, wb1))), Ad.calm.n(hi, 1n, 0n)) == True{} : Bool}
      {==}

def ad.adm_ia1(+l: Ad.Lim, +hi: Nat, +w: Nat, +wb1: Nat, u: Bool, er: {Ad.room(l, Nat.add(hi, 0n)) == False{} : Bool}) -> {LABool.ad.ok.n(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(False{}, u)}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(False{}, u)}), 1n+w), 0n, wb1) == True{} : Bool}:
  match u:
    case True{}:
      %Equal.sym(Bool, Ad.room(l, Nat.add(hi, 0n)), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 1n+w, hi, wb1))), Ad.calm.n(hi, 1n+w, 0n)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Ad.room(l, Nat.add(hi, 0n)), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 2n+w, hi, wb1))), Ad.calm.n(hi, 2n+w, 0n)) == True{} : Bool}
      {==}

# a background admit: a slot only when no request holds one
# interactively or waits
def ad.adm_bg0(+l: Ad.Lim, +hb: Nat, r: Bool, er: {Ad.room(l, hb) == r : Bool}) -> {LABool.ad.ok.n(l, 0n, 0n, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(r)}), hb), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(r)}), 0n)) == True{} : Bool}:
  match r:
    case True{}:
      +rr = Ad.room(l, 1n+hb)
      %Equal.sym(Maybe<&2, Ad.Cls>, Ad.pick.go(rr, 0n, 0n, 0n), None{}, LAAdmissionMisc.ad.pick_none0(rr, 0n)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(0n, 0n, 1n+hb)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Ad.room(l, hb), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 0n, 0n, 1n))), Ad.calm.n(0n, 0n, hb)) == True{} : Bool}
      LABool.ad.or_t(Ad.isz(hb))

def ad.adm_bg(+l: Ad.Lim, +hi: Nat, +wi: Nat, +wb: Nat, +hb: Nat, h: {LABool.ad.ok.n(l, hi, wi, hb, wb) == True{} : Bool}) -> {LABool.ad.ok.n(l, hi, wi, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))}), hb), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))}), wb)) == True{} : Bool}:
  match hi:
    case 1n+a:
      +rr = Ad.room(l, Nat.add(1n+a, hb))
      %LAAdmissionMisc.ad.pick_hi(rr, wi, a, wb, 1n+wb) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(1n+a, wi, hb)) == True{} : Bool}
      h
    case 0n:
      match wi:
        case 1n+b:
          +rr = Ad.room(l, hb)
          %LAAdmissionMisc.ad.pick_wi(rr, b, 0n, wb, 1n+wb) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(0n, 1n+b, hb)) == True{} : Bool}
          h
        case 0n:
          match wb:
            case 1n+c:
              +rr = Ad.room(l, hb)
              %LAAdmissionMisc.ad.pick_wb(rr, c, 1n+c) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(0n, 0n, hb)) == True{} : Bool}
              h
            case 0n:
              ad.adm_bg0(l, hb, Ad.room(l, hb), {==})

def ad.adm_bg_ok(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, h: {LABool.ad.ok(l, ts) == True{} : Bool}) -> {LABool.ad.ok(l, Ad.admit.bg(l, ts)) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
  +st = Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))
  +y = {Ad.Tk{Ad.Bg{}, st} : Ad.Tk}
  +t2 = List.append(&2, Ad.Tk, ts, [y])
  LABool.ad.ok.tr(l, hi, wi, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, y), hb), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, y), wb), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), hi, ad.app_off(Ad.Holding{}, Ad.Ia{}, ts, y, LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, st)))), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), wi, ad.app_off(Ad.Waiting{}, Ad.Ia{}, ts, y, LABool.ad.and_f(Ad.Mode.of(Ad.Waiting{}, st)))), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, y), hb), ad.cnt_app(Ad.Holding{}, Ad.Bg{}, ts, y)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, y), wb), ad.cnt_app(Ad.Waiting{}, Ad.Bg{}, ts, y)), ad.adm_bg(l, hi, wi, wb, hb, h))

# the ticket ops, by the ticket's status
def ad.col_ok(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, h: {LABool.ad.ok(l, ts) == True{} : Bool}) -> {LABool.ad.okS(Ad.collect.at(mb, l, q, ts, k)) == True{} : Bool}:
  match mb:
    case None{}:
      h
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      h
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      +t2 = Ad.put(ts, k, Ad.Held{})
      LABool.ad.ok.tr(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), ad.col_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), ad.col_cnt(Ad.Waiting{}, Ad.Ia{}, ts, k, c, e)), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), ad.col_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), ad.col_cnt(Ad.Waiting{}, Ad.Bg{}, ts, k, c, e)), h)
    case Some{Ad.Tk{c, Ad.Held{}}}:
      h
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      h
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      h

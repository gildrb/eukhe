# eukhe: lemmas the proofs of area admission share: admission/pick

import Base
import ../../../../bend/admission.bend as Ad
import ./calm.bend as LAAdmissionCalm
import ./cnt.bend as LAAdmissionCnt
import ./isz.bend as LAAdmissionIsz
import ./le.bend as LAAdmissionLe
import ../bool.bend as LABool
import ../logic.bend as LALogic
import ../nat.bend as LANat

def ad.pick_none0(r: Bool, hi: Nat) -> {Ad.pick.go(r, 0n, hi, 0n) == None{} : Maybe<&2, Ad.Cls>}:
  match r hi:
    case False{} _:
      {==}
    case True{} 0n:
      {==}
    case True{} 1n+x:
      {==}

def ad.pick_none_hi(r: Bool, -hi: Nat, -wb: Nat) -> {Ad.pick.go(r, 0n, 1n+hi, wb) == None{} : Maybe<&2, Ad.Cls>}:
  match r:
    case False{}:
      {==}
    case True{}:
      {==}

# with interactive slots held, background waiters do not matter
def ad.pick_hi(r: Bool, wi: Nat, -a: Nat, -x: Nat, -y: Nat) -> {Ad.pick.go(r, wi, 1n+a, x) == Ad.pick.go(r, wi, 1n+a, y) : Maybe<&2, Ad.Cls>}:
  match r wi:
    case False{} _:
      {==}
    case True{} 0n:
      {==}
    case True{} 1n+b:
      {==}

# with interactive waiters, background waiters do not matter
def ad.pick_wi(r: Bool, -b: Nat, -h: Nat, -x: Nat, -y: Nat) -> {Ad.pick.go(r, 1n+b, h, x) == Ad.pick.go(r, 1n+b, h, y) : Maybe<&2, Ad.Cls>}:
  match r:
    case False{}:
      {==}
    case True{}:
      {==}

def ad.pick_wb(r: Bool, -x: Nat, -y: Nat) -> {Ad.pick.go(r, 0n, 0n, 1n+x) == Ad.pick.go(r, 0n, 0n, 1n+y) : Maybe<&2, Ad.Cls>}:
  match r:
    case False{}:
      {==}
    case True{}:
      {==}

# an interactive admit: after the preemption a slot goes to it only
# while no interactive request waits; else no slot is free
def ad.adm_ia0(+l: Ad.Lim, +hi: Nat, +wb1: Nat, r: Bool, u: Bool, er: {Ad.room(l, hi) == r : Bool}) -> {LALogic.ad.ok.n(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(r, u)}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(r, u)}), 0n), 0n, wb1) == True{} : Bool}:
  match r u:
    case True{} _:
      +rr = Ad.room(l, Nat.add(1n+hi, 0n))
      %Equal.sym(Maybe<&2, Ad.Cls>, Ad.pick.go(rr, 0n, 1n+hi, wb1), None{}, ad.pick_none_hi(rr, hi, wb1)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(1n+hi, 0n, 0n)) == True{} : Bool}
      {==}
    case False{} True{}:
      %Equal.sym(Nat, Nat.add(hi, 0n), hi, LANat.ad.add_zero(hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, _), 0n, hi, wb1))), Ad.calm.n(hi, 0n, 0n)) == True{} : Bool}
      %Equal.sym(Bool, Ad.room(l, hi), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 0n, hi, wb1))), Ad.calm.n(hi, 0n, 0n)) == True{} : Bool}
      {==}
    case False{} False{}:
      %Equal.sym(Nat, Nat.add(hi, 0n), hi, LANat.ad.add_zero(hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, _), 1n, hi, wb1))), Ad.calm.n(hi, 1n, 0n)) == True{} : Bool}
      %Equal.sym(Bool, Ad.room(l, hi), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 1n, hi, wb1))), Ad.calm.n(hi, 1n, 0n)) == True{} : Bool}
      {==}

# a background admit: a slot only when no request holds one
# interactively or waits
def ad.adm_bg0(+l: Ad.Lim, +hb: Nat, r: Bool, er: {Ad.room(l, hb) == r : Bool}) -> {LALogic.ad.ok.n(l, 0n, 0n, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(r)}), hb), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(r)}), 0n)) == True{} : Bool}:
  match r:
    case True{}:
      +rr = Ad.room(l, 1n+hb)
      %Equal.sym(Maybe<&2, Ad.Cls>, Ad.pick.go(rr, 0n, 0n, 0n), None{}, ad.pick_none0(rr, 0n)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(0n, 0n, 1n+hb)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Ad.room(l, hb), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 0n, 0n, 1n))), Ad.calm.n(0n, 0n, hb)) == True{} : Bool}
      LABool.ad.or_t(Ad.isz(hb))

def ad.adm_bg(+l: Ad.Lim, +hi: Nat, +wi: Nat, +wb: Nat, +hb: Nat, h: {LALogic.ad.ok.n(l, hi, wi, hb, wb) == True{} : Bool}) -> {LALogic.ad.ok.n(l, hi, wi, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))}), hb), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))}), wb)) == True{} : Bool}:
  match hi:
    case 1n+a:
      +rr = Ad.room(l, Nat.add(1n+a, hb))
      %ad.pick_hi(rr, wi, a, wb, 1n+wb) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(1n+a, wi, hb)) == True{} : Bool}
      h
    case 0n:
      match wi:
        case 1n+b:
          +rr = Ad.room(l, hb)
          %ad.pick_wi(rr, b, 0n, wb, 1n+wb) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(0n, 1n+b, hb)) == True{} : Bool}
          h
        case 0n:
          match wb:
            case 1n+c:
              +rr = Ad.room(l, hb)
              %ad.pick_wb(rr, c, 1n+c) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(0n, 0n, hb)) == True{} : Bool}
              h
            case 0n:
              ad.adm_bg0(l, hb, Ad.room(l, hb), {==})

def ad.adm_bg_ok(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, h: {LALogic.ad.ok(l, ts) == True{} : Bool}) -> {LALogic.ad.ok(l, Ad.admit.bg(l, ts)) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
  +st = Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))
  +y = {Ad.Tk{Ad.Bg{}, st} : Ad.Tk}
  +t2 = List.append(&2, Ad.Tk, ts, [y])
  LALogic.ad.ok.tr(l, hi, wi, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, y), hb), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, y), wb), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), hi, LAAdmissionCnt.ad.app_off(Ad.Holding{}, Ad.Ia{}, ts, y, LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, st)))), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), wi, LAAdmissionCnt.ad.app_off(Ad.Waiting{}, Ad.Ia{}, ts, y, LABool.ad.and_f(Ad.Mode.of(Ad.Waiting{}, st)))), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, y), hb), LAAdmissionCnt.ad.cnt_app(Ad.Holding{}, Ad.Bg{}, ts, y)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, y), wb), LAAdmissionCnt.ad.cnt_app(Ad.Waiting{}, Ad.Bg{}, ts, y)), ad.adm_bg(l, hi, wi, wb, hb, h))

# A grant keeps the invariant
# ---------------------------

def ad.ok_idle(+l: Ad.Lim, +hi: Nat, +hb: Nat, c: {Ad.calm.n(hi, 0n, hb) == True{} : Bool}) -> {LALogic.ad.ok.n(l, hi, 0n, hb, 0n) == True{} : Bool}:
  +r = Ad.room(l, Nat.add(hi, hb))
  %Equal.sym(Maybe<&2, Ad.Cls>, Ad.pick.go(r, 0n, hi, 0n), None{}, ad.pick_none0(r, hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(hi, 0n, hb)) == True{} : Bool}
  c

def ad.grant_idle(+l: Ad.Lim, +t: List<&2, Ad.Tk>, z: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t) == 0n : Nat}, cm: {Ad.calm(t) == True{} : Bool}) -> {LALogic.ad.ok(l, t) == True{} : Bool}:
  (+zi, zb) = z
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)
  LALogic.ad.ok.tr(l, hi, 0n, hb, 0n, hi, wi, hb, wb, {==}, Equal.sym(Nat, wi, 0n, zi), {==}, Equal.sym(Nat, wb, 0n, zb), ad.ok_idle(l, hi, hb, LAAdmissionCalm.ad.calm.tr(hi, wi, hb, hi, 0n, hb, {==}, zi, {==}, cm)))

def ad.grant_ok(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +ed: {Ad.pick(l, t) == d : Maybe<&2, Ad.Cls>}, fuel: {Ad.le(Ad.waits(t), n) == True{} : Bool}, +cm: {Ad.calm(t) == True{} : Bool}) -> {LALogic.ad.ok(l, Ad.grant.go(n, d, l, t)) == True{} : Bool}:
  match n d:
    case 0n _:
      ad.grant_idle(l, t, LALogic.ad.zero2(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), fuel), cm)
    case 1n+f None{}:
      LABool.ad.grant_none(l, t, ed, cm)
    case 1n+f Some{Ad.Ia{}}:
      +nz = LAAdmissionIsz.ad.pick_ia(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), ed)
      ad.grant_ok(f, Ad.pick(l, Ad.mark(Ad.Ia{}, t)), l, Ad.mark(Ad.Ia{}, t), {==}, LAAdmissionLe.ad.fuel_ia(t, f, nz, fuel), LAAdmissionCalm.ad.calm_mark_ia(t, nz, cm))
    case 1n+f Some{Ad.Bg{}}:
      ad.grant_ok(f, Ad.pick(l, Ad.mark(Ad.Bg{}, t)), l, Ad.mark(Ad.Bg{}, t), {==}, LAAdmissionLe.ad.fuel_bg(t, f, LAAdmissionCnt.ad.bg_wi(t, LAAdmissionIsz.ad.pbg(l, t, ed)), LAAdmissionIsz.ad.bg_wb(t, LAAdmissionIsz.ad.pbg(l, t, ed)), fuel), LAAdmissionCalm.ad.calm_bg(t, LAAdmissionCnt.ad.bg_wi(t, LAAdmissionIsz.ad.pbg(l, t, ed)), LAAdmissionCnt.ad.bg_hi(t, LAAdmissionIsz.ad.pbg(l, t, ed)), LAAdmissionIsz.ad.bg_wb(t, LAAdmissionIsz.ad.pbg(l, t, ed))))

# a ticket ends, then the waiters are granted
def ad.end_grant(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, +s: Ad.Sts, +e: {Ad.get(ts, k) == Some{Ad.Tk{c, s}} : Maybe<&2, Ad.Tk>}, cm: {Ad.calm(ts) == True{} : Bool}) -> {LALogic.ad.ok(l, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))) == True{} : Bool}:
  +t2 = Ad.put(ts, k, Ad.Ended{})
  ad.grant_ok(Ad.waits(t2), Ad.pick(l, t2), l, t2, {==}, LAAdmissionLe.ad.le_refl(Ad.waits(t2)), LAAdmissionCalm.ad.end_calm(ts, k, c, s, e, cm))

def ad.lea_ok(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, +h: {LALogic.ad.ok(l, ts) == True{} : Bool}) -> {LALogic.ad.okS(Ad.leave.at(mb, l, q, ts, k)) == True{} : Bool}:
  match mb:
    case None{}:
      h
    case Some{Ad.Tk{+c, Ad.Queued{}}}:
      ad.end_grant(l, ts, k, c, Ad.Queued{}, e, LAAdmissionCalm.ad.calm_of(l, ts, h))
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      ad.end_grant(l, ts, k, c, Ad.Granted{}, e, LAAdmissionCalm.ad.calm_of(l, ts, h))
    case Some{Ad.Tk{c, Ad.Held{}}}:
      h
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      h
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      h

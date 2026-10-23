# eukhe: lemmas the proofs of area admission share: admission/le

import Base
import ../../../../bend/admission.bend as Ad
import ./bit.bend as LAAdmissionBit
import ./calm.bend as LAAdmissionCalm
import ./misc.bend as LAAdmissionMisc
import ../bool.bend as LABool

def ad.le_refl(n: Nat) -> {Ad.le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ad.le_refl(p)

def ad.zero2(a: Nat, b: Nat, e: {Ad.le(Nat.add(a, b), 0n) == True{} : Bool}) -> {a == 0n : Nat} & {b == 0n : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          ({==}, {==})
        case 1n+y:
          LABool.ad.absurd({0n == 0n : Nat} & {1n+y == 0n : Nat}, e)
    case 1n+x:
      LABool.ad.absurd({1n+x == 0n : Nat} & {b == 0n : Nat}, e)

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

def ad.grant_ok(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +ed: {Ad.pick(l, t) == d : Maybe<&2, Ad.Cls>}, fuel: {Ad.le(Ad.waits(t), n) == True{} : Bool}, +cm: {Ad.calm(t) == True{} : Bool}) -> {LABool.ad.ok(l, Ad.grant.go(n, d, l, t)) == True{} : Bool}:
  match n d:
    case 0n _:
      LAAdmissionCalm.ad.grant_idle(l, t, ad.zero2(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), fuel), cm)
    case 1n+f None{}:
      LAAdmissionMisc.ad.grant_none(l, t, ed, cm)
    case 1n+f Some{Ad.Ia{}}:
      +nz = LAAdmissionMisc.ad.pick_ia(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), ed)
      ad.grant_ok(f, Ad.pick(l, Ad.mark(Ad.Ia{}, t)), l, Ad.mark(Ad.Ia{}, t), {==}, ad.fuel_ia(t, f, nz, fuel), LAAdmissionCalm.ad.calm_mark_ia(t, nz, cm))
    case 1n+f Some{Ad.Bg{}}:
      ad.grant_ok(f, Ad.pick(l, Ad.mark(Ad.Bg{}, t)), l, Ad.mark(Ad.Bg{}, t), {==}, ad.fuel_bg(t, f, LAAdmissionMisc.ad.bg_wi(t, LAAdmissionMisc.ad.pbg(l, t, ed)), LAAdmissionMisc.ad.bg_wb(t, LAAdmissionMisc.ad.pbg(l, t, ed)), fuel), LAAdmissionCalm.ad.calm_bg(t, LAAdmissionMisc.ad.bg_wi(t, LAAdmissionMisc.ad.pbg(l, t, ed)), LAAdmissionMisc.ad.bg_hi(t, LAAdmissionMisc.ad.pbg(l, t, ed)), LAAdmissionMisc.ad.bg_wb(t, LAAdmissionMisc.ad.pbg(l, t, ed))))

# a ticket ends, then the waiters are granted
def ad.end_grant(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, +s: Ad.Sts, +e: {Ad.get(ts, k) == Some{Ad.Tk{c, s}} : Maybe<&2, Ad.Tk>}, cm: {Ad.calm(ts) == True{} : Bool}) -> {LABool.ad.ok(l, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))) == True{} : Bool}:
  +t2 = Ad.put(ts, k, Ad.Ended{})
  ad.grant_ok(Ad.waits(t2), Ad.pick(l, t2), l, t2, {==}, ad.le_refl(Ad.waits(t2)), LAAdmissionCalm.ad.end_calm(ts, k, c, s, e, cm))

def ad.rel_ok(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, +h: {LABool.ad.ok(l, ts) == True{} : Bool}) -> {LABool.ad.okS(Ad.release.at(mb, l, q, ts, k)) == True{} : Bool}:
  match mb:
    case None{}:
      h
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      h
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      h
    case Some{Ad.Tk{+c, Ad.Held{}}}:
      ad.end_grant(l, ts, k, c, Ad.Held{}, e, LAAdmissionCalm.ad.calm_of(l, ts, h))
    case Some{Ad.Tk{+c, Ad.Preempted{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      LABool.ad.ok.tr(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, Ad.Preempted{}, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Waiting{}, Ad.Ia{}, ts, k, c, Ad.Preempted{}, e)), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, Ad.Preempted{}, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Waiting{}, Ad.Bg{}, ts, k, c, Ad.Preempted{}, e)), h)
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      h

def ad.lea_ok(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, +h: {LABool.ad.ok(l, ts) == True{} : Bool}) -> {LABool.ad.okS(Ad.leave.at(mb, l, q, ts, k)) == True{} : Bool}:
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

def ad.step_ok(s: Ad.St, o: Ad.Op, +h: {LABool.ad.okS(s) == True{} : Bool}) -> {LABool.ad.okS(Ad.step(s, o)) == True{} : Bool}:
  match s:
    case Ad.St{+l, +q, +ts}:
      match o:
        case Ad.Admit{Ad.Ia{}}:
          LAAdmissionCalm.ad.adm_ia_ok(l, q, ts, h)
        case Ad.Admit{Ad.Bg{}}:
          LAAdmissionBit.ad.adm_bg_ok(l, ts, h)
        case Ad.Collect{+k}:
          LAAdmissionBit.ad.col_ok(Ad.get(ts, k), l, q, ts, k, {==}, h)
        case Ad.Release{+k}:
          ad.rel_ok(Ad.get(ts, k), l, q, ts, k, {==}, h)
        case Ad.Leave{+k}:
          ad.lea_ok(Ad.get(ts, k), l, q, ts, k, {==}, h)
        case Ad.Limit{+l2, q2}:
          ad.grant_ok(Ad.waits(ts), Ad.pick(l2, ts), l2, ts, {==}, ad.le_refl(Ad.waits(ts)), LAAdmissionCalm.ad.calm_of(l, ts, h))

def ad.run_ok(os: List<&2, Ad.Op>, +s: Ad.St, h: {LABool.ad.okS(s) == True{} : Bool}) -> {LABool.ad.okS(Ad.run(os, s)) == True{} : Bool}:
  match os:
    case Nil{}:
      h
    case +o <> r:
      ad.run_ok(r, Ad.step(s, o), ad.step_ok(s, o, h))

# Slots held stay within the limit
# --------------------------------

def ad.le_trans(a: Nat, b: Nat, c: Nat, ab: {Ad.le(a, b) == True{} : Bool}, bc: {Ad.le(b, c) == True{} : Bool}) -> {Ad.le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      {==}
    case 1n+x 0n _:
      LABool.ad.absurd({Ad.le(1n+x, c) == True{} : Bool}, ab)
    case 1n+x 1n+y 0n:
      LABool.ad.absurd({Ad.le(1n+x, 0n) == True{} : Bool}, bc)
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
          LABool.ad.absurd({Ad.le(1n+a, 1n) == True{} : Bool}, e)
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

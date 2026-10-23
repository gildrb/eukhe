# eukhe: lemmas the proofs of area admission share

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base.bend as L
import ./adw_cls_round_trip.bend as PAdwClsRoundTrip

# ---- admission ----

# proof_admission: the admission laws of LAWS.bend (rule H3 of
# docs/harness.md) over the model in admission.bend.

# Logic
# -----

# a type picked by a Bool: a rewrite through it refutes False == True
def ad.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ad.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ad.BD(_, A, Unit)
  Unit{}

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

# what a count of mode m, class c sees of ticket mb
def ad.at(+m: Ad.Mode, +c: Ad.Cls, mb: Maybe<&2, Ad.Tk>) -> Bool:
  match mb:
    case None{}:
      False{}
    case Some{t}:
      Ad.hit(m, c, t)

# ticket mb with status x
def ad.set(mb: Maybe<&2, Ad.Tk>, x: Ad.Sts) -> Maybe<&2, Ad.Tk>:
  match mb:
    case None{}:
      None{}
    case Some{Ad.Tk{c, s}}:
      Some{Ad.Tk{c, x}}

# a ticket's new status counts in its place
def ad.cnt_put(+m: Ad.Mode, +c: Ad.Cls, t: List<&2, Ad.Tk>, +k: Nat, +x: Ad.Sts) -> {Ad.bit(ad.at(m, c, Ad.get(t, k)), Ad.cnt(m, c, Ad.put(t, k, x))) == Ad.bit(ad.at(m, c, ad.set(Ad.get(t, k), x)), Ad.cnt(m, c, t)) : Nat}:
  match t:
    case Nil{}:
      {==}
    case Ad.Tk{+c1, +s1} <> +r:
      match k:
        case 0n:
          ad.bit_comm(Ad.hit(m, c, Ad.Tk{c1, s1}), Ad.hit(m, c, Ad.Tk{c1, x}), Ad.cnt(m, c, r))
        case 1n+p:
          +ha = ad.at(m, c, Ad.get(r, p))
          +hs = ad.at(m, c, ad.set(Ad.get(r, p), x))
          +hh = Ad.hit(m, c, Ad.Tk{c1, s1})
          %ad.bit_comm(hh, ha, Ad.cnt(m, c, Ad.put(r, p, x))) : {_ == Ad.bit(hs, Ad.bit(hh, Ad.cnt(m, c, r))) : Nat}
          %Equal.sym(Nat, Ad.bit(ha, Ad.cnt(m, c, Ad.put(r, p, x))), Ad.bit(hs, Ad.cnt(m, c, r)), ad.cnt_put(m, c, r, p, x)) : {Ad.bit(hh, _) == Ad.bit(hs, Ad.bit(hh, Ad.cnt(m, c, r))) : Nat}
          ad.bit_comm(hh, hs, Ad.cnt(m, c, r))

def ad.absurd_t(-A: Type, e: {True{} == False{} : Bool}) -> A:
  ad.absurd(A, Equal.sym(Bool, True{}, False{}, e))

def ad.and_ff(x: Bool, y: Bool) -> {Bool.and(x, False{}) == Bool.and(y, False{}) : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ad.and_f(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

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
          ad.and_ff(Ad.Mode.of(m, Ad.Queued{}), Ad.Mode.of(m, Ad.Granted{}))
        case Ad.Held{}:
          ad.and_ff(Ad.Mode.of(m, Ad.Preempted{}), Ad.Mode.of(m, Ad.Held{}))
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
      ad.and_f(Ad.Mode.of(Ad.Holding{}, s))
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
      ad.absurd_t({Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Queued{}}), 0n) == Ad.bit(Ad.hit(m, d, Ad.Tk{c, Ad.Granted{}}), 0n) : Nat}, nz)
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

# Bools and numbers
# -----------------

def ad.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ad.absurd({False{} == True{} : Bool}, e)

def ad.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      ad.absurd({b == True{} : Bool}, e)

def ad.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      ad.absurd({Bool.and(False{}, b) == True{} : Bool}, ea)

def ad.or_t(x: Bool) -> {Bool.or(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def ad.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def ad.bit_inj(b: Bool, -x: Nat, -y: Nat, e: {Ad.bit(b, x) == Ad.bit(b, y) : Nat}) -> {x == y : Nat}:
  match b:
    case False{}:
      e
    case True{}:
      Equal.cong(Nat, Nat, n => ad.pred(n), 1n+x, 1n+y, e)

def ad.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %ad.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

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
          ad.absurd({0n == 0n : Nat} & {1n+y == 0n : Nat}, e)
    case 1n+x:
      ad.absurd({1n+x == 0n : Nat} & {b == 0n : Nat}, e)

# a Some{c} that is not: refuted through its class
def ad.mis(m: Maybe<&2, Ad.Cls>, c: Ad.Cls) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{d}:
      Ad.Cls.eq(d, c)

def ad.m_ia(-X: Type, -m: Maybe<&2, Ad.Cls>, e: {m == Some{Ad.Ia{}} : Maybe<&2, Ad.Cls>}, u: ad.BD(ad.mis(m, Ad.Ia{}), X, Unit)) -> X:
  %e : ad.BD(ad.mis(_, Ad.Ia{}), X, Unit)
  u

def ad.m_bg(-X: Type, -m: Maybe<&2, Ad.Cls>, e: {m == Some{Ad.Bg{}} : Maybe<&2, Ad.Cls>}, u: ad.BD(ad.mis(m, Ad.Bg{}), X, Unit)) -> X:
  %e : ad.BD(ad.mis(_, Ad.Bg{}), X, Unit)
  u

# The invariant: no lost wake-up, and background slots only while no
# interactive request holds or waits
# ------------------------------------------------------------------

def ad.ok.n(+l: Ad.Lim, +hi: Nat, +wi: Nat, +hb: Nat, +wb: Nat) -> Bool:
  Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, Nat.add(hi, hb)), wi, hi, wb))), Ad.calm.n(hi, wi, hb))

def ad.ok(+l: Ad.Lim, +ts: List<&2, Ad.Tk>) -> Bool:
  ad.ok.n(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts))

def ad.okS(s: Ad.St) -> Bool:
  match s:
    case Ad.St{+l, q, +ts}:
      ad.ok(l, ts)

def ad.ok.tr(-l: Ad.Lim, -a1: Nat, -a2: Nat, -a3: Nat, -a4: Nat, -b1: Nat, -b2: Nat, -b3: Nat, -b4: Nat, e1: {a1 == b1 : Nat}, e2: {a2 == b2 : Nat}, e3: {a3 == b3 : Nat}, e4: {a4 == b4 : Nat}, h: {ad.ok.n(l, a1, a2, a3, a4) == True{} : Bool}) -> {ad.ok.n(l, b1, b2, b3, b4) == True{} : Bool}:
  %e1 : {ad.ok.n(l, _, b2, b3, b4) == True{} : Bool}
  %e2 : {ad.ok.n(l, a1, _, b3, b4) == True{} : Bool}
  %e3 : {ad.ok.n(l, a1, a2, _, b4) == True{} : Bool}
  %e4 : {ad.ok.n(l, a1, a2, a3, _) == True{} : Bool}
  h

def ad.calm.tr(-a1: Nat, -a2: Nat, -a3: Nat, -b1: Nat, -b2: Nat, -b3: Nat, e1: {a1 == b1 : Nat}, e2: {a2 == b2 : Nat}, e3: {a3 == b3 : Nat}, h: {Ad.calm.n(a1, a2, a3) == True{} : Bool}) -> {Ad.calm.n(b1, b2, b3) == True{} : Bool}:
  %e1 : {Ad.calm.n(_, b2, b3) == True{} : Bool}
  %e2 : {Ad.calm.n(a1, _, b3) == True{} : Bool}
  %e3 : {Ad.calm.n(a1, a2, _) == True{} : Bool}
  h

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

# a grant to an interactive waiter: one waits
def ad.pick_ia(r: Bool, wi: Nat, hi: Nat, wb: Nat, e: {Ad.pick.go(r, wi, hi, wb) == Some{Ad.Ia{}} : Maybe<&2, Ad.Cls>}) -> {Ad.isz(wi) == False{} : Bool}:
  match r wi hi wb:
    case False{} _ _ _:
      ad.m_ia({Ad.isz(wi) == False{} : Bool}, None{}, e, Unit{})
    case True{} 1n+a _ _:
      {==}
    case True{} 0n 1n+b _:
      ad.m_ia({Ad.isz(0n) == False{} : Bool}, None{}, e, Unit{})
    case True{} 0n 0n 0n:
      ad.m_ia({Ad.isz(0n) == False{} : Bool}, None{}, e, Unit{})
    case True{} 0n 0n 1n+d:
      ad.m_ia({Ad.isz(0n) == False{} : Bool}, Some{Ad.Bg{}}, e, Unit{})

# a grant to a background waiter: no interactive request holds or waits,
# and one background request waits
def ad.pick_bg(r: Bool, wi: Nat, hi: Nat, wb: Nat, e: {Ad.pick.go(r, wi, hi, wb) == Some{Ad.Bg{}} : Maybe<&2, Ad.Cls>}) -> {wi == 0n : Nat} & ({hi == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}):
  match r wi hi wb:
    case False{} _ _ _:
      ad.m_bg({wi == 0n : Nat} & ({hi == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}), None{}, e, Unit{})
    case True{} 1n+a _ _:
      ad.m_bg({1n+a == 0n : Nat} & ({hi == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}), Some{Ad.Ia{}}, e, Unit{})
    case True{} 0n 1n+b _:
      ad.m_bg({0n == 0n : Nat} & ({1n+b == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}), None{}, e, Unit{})
    case True{} 0n 0n 0n:
      ad.m_bg({0n == 0n : Nat} & ({0n == 0n : Nat} & {Ad.isz(0n) == False{} : Bool}), None{}, e, Unit{})
    case True{} 0n 0n 1n+d:
      ({==}, ({==}, {==}))

# calm stays calm as counts drop
def ad.calm_m1(-a: Nat, -b: Nat, c: Nat, h: {Ad.calm.n(1n+a, b, c) == True{} : Bool}) -> {Ad.calm.n(a, b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      ad.absurd({Ad.calm.n(a, b, 1n+x) == True{} : Bool}, h)

def ad.calm_m2(+a: Nat, -b: Nat, c: Nat, h: {Ad.calm.n(a, 1n+b, c) == True{} : Bool}) -> {Ad.calm.n(a, b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      ad.absurd({Ad.calm.n(a, b, 1n+x) == True{} : Bool}, Equal.trans(Bool, False{}, Bool.and(Ad.isz(a), False{}), True{}, Equal.sym(Bool, Bool.and(Ad.isz(a), False{}), False{}, ad.and_f(Ad.isz(a))), h))

def ad.calm_m3(-a: Nat, -b: Nat, c: Nat, h: {Ad.calm.n(a, b, 1n+c) == True{} : Bool}) -> {Ad.calm.n(a, b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      h

def ad.calm_mono(x1: Bool, x2: Bool, x3: Bool, +a: Nat, +b: Nat, +c: Nat, h: {Ad.calm.n(Ad.bit(x1, a), Ad.bit(x2, b), Ad.bit(x3, c)) == True{} : Bool}) -> {Ad.calm.n(a, b, c) == True{} : Bool}:
  match x1 x2 x3:
    case False{} False{} False{}:
      h
    case False{} False{} True{}:
      ad.calm_m3(a, b, c, h)
    case False{} True{} False{}:
      ad.calm_m2(a, b, c, h)
    case False{} True{} True{}:
      ad.calm_m3(a, b, c, ad.calm_m2(a, b, 1n+c, h))
    case True{} False{} False{}:
      ad.calm_m1(a, b, c, h)
    case True{} False{} True{}:
      ad.calm_m3(a, b, c, ad.calm_m1(a, b, 1n+c, h))
    case True{} True{} False{}:
      ad.calm_m2(a, b, c, ad.calm_m1(a, 1n+b, c, h))
    case True{} True{} True{}:
      ad.calm_m3(a, b, c, ad.calm_m2(a, b, 1n+c, ad.calm_m1(a, 1n+b, 1n+c, h)))

# an interactive waiter: no background slot is held
def ad.calm_hb0(+hi: Nat, -w: Nat, hb: Nat, c: {Ad.calm.n(hi, 1n+w, hb) == True{} : Bool}) -> {hb == 0n : Nat}:
  match hb:
    case 0n:
      {==}
    case 1n+x:
      ad.absurd({1n+x == 0n : Nat}, Equal.trans(Bool, False{}, Bool.and(Ad.isz(hi), False{}), True{}, Equal.sym(Bool, Bool.and(Ad.isz(hi), False{}), False{}, ad.and_f(Ad.isz(hi))), c))

# an interactive waiter: no slot is free
def ad.ok_room(r: Bool, -w: Nat, -hi: Nat, -wb: Nat, -c: Bool, h: {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(r, 1n+w, hi, wb))), c) == True{} : Bool}) -> {r == False{} : Bool}:
  match r:
    case True{}:
      ad.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# A grant keeps the invariant
# ---------------------------

def ad.ok_idle(+l: Ad.Lim, +hi: Nat, +hb: Nat, c: {Ad.calm.n(hi, 0n, hb) == True{} : Bool}) -> {ad.ok.n(l, hi, 0n, hb, 0n) == True{} : Bool}:
  +r = Ad.room(l, Nat.add(hi, hb))
  %Equal.sym(Maybe<&2, Ad.Cls>, Ad.pick.go(r, 0n, hi, 0n), None{}, ad.pick_none0(r, hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(hi, 0n, hb)) == True{} : Bool}
  c

def ad.grant_idle(+l: Ad.Lim, +t: List<&2, Ad.Tk>, z: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t) == 0n : Nat}, cm: {Ad.calm(t) == True{} : Bool}) -> {ad.ok(l, t) == True{} : Bool}:
  (+zi, zb) = z
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)
  ad.ok.tr(l, hi, 0n, hb, 0n, hi, wi, hb, wb, {==}, Equal.sym(Nat, wi, 0n, zi), {==}, Equal.sym(Nat, wb, 0n, zb), ad.ok_idle(l, hi, hb, ad.calm.tr(hi, wi, hb, hi, 0n, hb, {==}, zi, {==}, cm)))

def ad.not_none(-m: Maybe<&2, Ad.Cls>, e: {m == None{} : Maybe<&2, Ad.Cls>}) -> {Bool.not(Maybe.is_some(&2, Ad.Cls, m)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Ad.Cls>, m, None{}, e) : {Bool.not(Maybe.is_some(&2, Ad.Cls, _)) == True{} : Bool}
  {==}

def ad.grant_none(+l: Ad.Lim, +t: List<&2, Ad.Tk>, ed: {Ad.pick(l, t) == None{} : Maybe<&2, Ad.Cls>}, cm: {Ad.calm(t) == True{} : Bool}) -> {ad.ok(l, t) == True{} : Bool}:
  +p = Ad.pick(l, t)
  ad.and_t(Bool.not(Maybe.is_some(&2, Ad.Cls, p)), Ad.calm(t), ad.not_none(p, ed), cm)

# the waiters bound the grants still to come
def ad.fuel_ia(+t: List<&2, Ad.Tk>, -f: Nat, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)) == False{} : Bool}, fuel: {Ad.le(Ad.waits(t), 1n+f) == True{} : Bool}) -> {Ad.le(Ad.waits(Ad.mark(Ad.Ia{}, t)), f) == True{} : Bool}:
  +t2 = Ad.mark(Ad.Ia{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)
  +wi2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +wb2 = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2)
  %Equal.sym(Nat, wb2, wb, ad.cnt_mark(Ad.Waiting{}, Ad.Bg{}, t, Ad.Ia{}, nz)) : {Ad.le(Nat.add(wi2, _), f) == True{} : Bool}
  %Equal.sym(Nat, 1n+wi2, wi, ad.cnt_mark(Ad.Waiting{}, Ad.Ia{}, t, Ad.Ia{}, nz)) : {Ad.le(Nat.add(_, wb), 1n+f) == True{} : Bool}
  fuel

def ad.calm_ia(-a: Nat, -b: Nat, hb: Nat, +hi: Nat, -w: Nat, c: {Ad.calm.n(hi, 1n+w, hb) == True{} : Bool}) -> {Ad.calm.n(a, b, hb) == True{} : Bool}:
  match hb:
    case 0n:
      {==}
    case 1n+x:
      ad.absurd({Ad.calm.n(a, b, 1n+x) == True{} : Bool}, Equal.trans(Bool, False{}, Bool.and(Ad.isz(hi), False{}), True{}, Equal.sym(Bool, Bool.and(Ad.isz(hi), False{}), False{}, ad.and_f(Ad.isz(hi))), c))

def ad.calm_mark_ia(+t: List<&2, Ad.Tk>, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)) == False{} : Bool}, cm: {Ad.calm(t) == True{} : Bool}) -> {Ad.calm(Ad.mark(Ad.Ia{}, t)) == True{} : Bool}:
  +t2 = Ad.mark(Ad.Ia{}, t)
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t)
  +hi2 = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2)
  +wi2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +hb2 = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)
  %Equal.sym(Nat, hb2, hb, ad.cnt_mark(Ad.Holding{}, Ad.Bg{}, t, Ad.Ia{}, nz)) : {Ad.calm.n(hi2, wi2, _) == True{} : Bool}
  ad.calm_ia(hi2, wi2, hb, hi, wi2, ad.calm.tr(hi, wi, hb, hi, 1n+wi2, hb, {==}, Equal.sym(Nat, 1n+wi2, wi, ad.cnt_mark(Ad.Waiting{}, Ad.Ia{}, t, Ad.Ia{}, nz)), {==}, cm))

def ad.pbg(+l: Ad.Lim, +t: List<&2, Ad.Tk>, e: {Ad.pick(l, t) == Some{Ad.Bg{}} : Maybe<&2, Ad.Cls>}) -> {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}):
  ad.pick_bg(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), e)

def ad.bg_wi(-t: List<&2, Ad.Tk>, p: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool})) -> {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat}:
  (a, b, c) = p
  a

def ad.bg_hi(-t: List<&2, Ad.Tk>, p: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool})) -> {Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat}:
  (a, b, c) = p
  b

def ad.bg_wb(-t: List<&2, Ad.Tk>, p: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool})) -> {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}:
  (a, b, c) = p
  c

def ad.fuel_bg(+t: List<&2, Ad.Tk>, -f: Nat, +zi: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat}, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}, fuel: {Ad.le(Ad.waits(t), 1n+f) == True{} : Bool}) -> {Ad.le(Ad.waits(Ad.mark(Ad.Bg{}, t)), f) == True{} : Bool}:
  +t2 = Ad.mark(Ad.Bg{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)
  +wi2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +wb2 = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2)
  %Equal.sym(Nat, wi2, wi, ad.cnt_mark(Ad.Waiting{}, Ad.Ia{}, t, Ad.Bg{}, nz)) : {Ad.le(Nat.add(_, wb2), f) == True{} : Bool}
  %Equal.sym(Nat, wi, 0n, zi) : {Ad.le(Nat.add(_, wb2), f) == True{} : Bool}
  %Equal.sym(Nat, 1n+wb2, wb, ad.cnt_mark(Ad.Waiting{}, Ad.Bg{}, t, Ad.Bg{}, nz)) : {Ad.le(_, 1n+f) == True{} : Bool}
  %zi : {Ad.le(Nat.add(_, wb), 1n+f) == True{} : Bool}
  fuel

def ad.calm_bg(+t: List<&2, Ad.Tk>, zi: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat}, zh: {Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat}, +nz: {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}) -> {Ad.calm(Ad.mark(Ad.Bg{}, t)) == True{} : Bool}:
  +t2 = Ad.mark(Ad.Bg{}, t)
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)
  +hi2 = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2)
  +wi2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +hb2 = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)
  %Equal.sym(Nat, hi2, hi, ad.cnt_mark(Ad.Holding{}, Ad.Ia{}, t, Ad.Bg{}, nz)) : {Ad.calm.n(_, wi2, hb2) == True{} : Bool}
  %Equal.sym(Nat, wi2, wi, ad.cnt_mark(Ad.Waiting{}, Ad.Ia{}, t, Ad.Bg{}, nz)) : {Ad.calm.n(hi, _, hb2) == True{} : Bool}
  %Equal.sym(Nat, hi, 0n, zh) : {Ad.calm.n(_, wi, hb2) == True{} : Bool}
  %Equal.sym(Nat, wi, 0n, zi) : {Ad.calm.n(0n, _, hb2) == True{} : Bool}
  ad.or_t(Ad.isz(hb2))

def ad.grant_ok(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +ed: {Ad.pick(l, t) == d : Maybe<&2, Ad.Cls>}, fuel: {Ad.le(Ad.waits(t), n) == True{} : Bool}, +cm: {Ad.calm(t) == True{} : Bool}) -> {ad.ok(l, Ad.grant.go(n, d, l, t)) == True{} : Bool}:
  match n d:
    case 0n _:
      ad.grant_idle(l, t, ad.zero2(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), fuel), cm)
    case 1n+f None{}:
      ad.grant_none(l, t, ed, cm)
    case 1n+f Some{Ad.Ia{}}:
      +nz = ad.pick_ia(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), ed)
      ad.grant_ok(f, Ad.pick(l, Ad.mark(Ad.Ia{}, t)), l, Ad.mark(Ad.Ia{}, t), {==}, ad.fuel_ia(t, f, nz, fuel), ad.calm_mark_ia(t, nz, cm))
    case 1n+f Some{Ad.Bg{}}:
      ad.grant_ok(f, Ad.pick(l, Ad.mark(Ad.Bg{}, t)), l, Ad.mark(Ad.Bg{}, t), {==}, ad.fuel_bg(t, f, ad.bg_wi(t, ad.pbg(l, t, ed)), ad.bg_wb(t, ad.pbg(l, t, ed)), fuel), ad.calm_bg(t, ad.bg_wi(t, ad.pbg(l, t, ed)), ad.bg_hi(t, ad.pbg(l, t, ed)), ad.bg_wb(t, ad.pbg(l, t, ed))))

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
  Equal.trans(Nat, Ad.cnt(m, Ad.Ia{}, List.append(&2, Ad.Tk, Ad.preempt(ts), [x])), Ad.bit(hx, Ad.cnt(m, Ad.Ia{}, Ad.preempt(ts))), Ad.bit(hx, Ad.cnt(m, Ad.Ia{}, ts)), ad.cnt_app(m, Ad.Ia{}, Ad.preempt(ts), x), Equal.cong(Nat, Nat, y => Ad.bit(hx, y), Ad.cnt(m, Ad.Ia{}, Ad.preempt(ts)), Ad.cnt(m, Ad.Ia{}, ts), ad.pre_ia(m, ts)))

def ad.put_at(+m: Ad.Mode, +cc: Ad.Cls, +ts: List<&2, Ad.Tk>, +k: Nat, +x: Ad.Sts, -mb: Maybe<&2, Ad.Tk>, e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}) -> {Ad.bit(ad.at(m, cc, mb), Ad.cnt(m, cc, Ad.put(ts, k, x))) == Ad.bit(ad.at(m, cc, ad.set(mb, x)), Ad.cnt(m, cc, ts)) : Nat}:
  %e : {Ad.bit(ad.at(m, cc, _), Ad.cnt(m, cc, Ad.put(ts, k, x))) == Ad.bit(ad.at(m, cc, ad.set(_, x)), Ad.cnt(m, cc, ts)) : Nat}
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

def ad.end_calm(+ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, +s: Ad.Sts, +e: {Ad.get(ts, k) == Some{Ad.Tk{c, s}} : Maybe<&2, Ad.Tk>}, cm: {Ad.calm(ts) == True{} : Bool}) -> {Ad.calm(Ad.put(ts, k, Ad.Ended{})) == True{} : Bool}:
  +t2 = Ad.put(ts, k, Ad.Ended{})
  +x = {Ad.Tk{c, s} : Ad.Tk}
  +x1 = Ad.hit(Ad.Holding{}, Ad.Ia{}, x)
  +x2 = Ad.hit(Ad.Waiting{}, Ad.Ia{}, x)
  +x3 = Ad.hit(Ad.Holding{}, Ad.Bg{}, x)
  +a1 = Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2)
  +a2 = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2)
  +a3 = Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2)
  ad.calm_mono(x1, x2, x3, a1, a2, a3, ad.calm.tr(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), Ad.bit(x1, a1), Ad.bit(x2, a2), Ad.bit(x3, a3), Equal.sym(Nat, Ad.bit(x1, a1), Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, s, e)), Equal.sym(Nat, Ad.bit(x2, a2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), ad.end_cnt(Ad.Waiting{}, Ad.Ia{}, ts, k, c, s, e)), Equal.sym(Nat, Ad.bit(x3, a3), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, s, e)), cm))

def ad.calm_of(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, h: {ad.ok(l, ts) == True{} : Bool}) -> {Ad.calm(ts) == True{} : Bool}:
  ad.and_r(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick(l, ts))), Ad.calm(ts), h)

# a ticket ends, then the waiters are granted
def ad.end_grant(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, +k: Nat, +c: Ad.Cls, +s: Ad.Sts, +e: {Ad.get(ts, k) == Some{Ad.Tk{c, s}} : Maybe<&2, Ad.Tk>}, cm: {Ad.calm(ts) == True{} : Bool}) -> {ad.ok(l, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))) == True{} : Bool}:
  +t2 = Ad.put(ts, k, Ad.Ended{})
  ad.grant_ok(Ad.waits(t2), Ad.pick(l, t2), l, t2, {==}, ad.le_refl(Ad.waits(t2)), ad.end_calm(ts, k, c, s, e, cm))

# an interactive admit: after the preemption a slot goes to it only
# while no interactive request waits; else no slot is free
def ad.adm_ia0(+l: Ad.Lim, +hi: Nat, +wb1: Nat, r: Bool, u: Bool, er: {Ad.room(l, hi) == r : Bool}) -> {ad.ok.n(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(r, u)}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(r, u)}), 0n), 0n, wb1) == True{} : Bool}:
  match r u:
    case True{} _:
      +rr = Ad.room(l, Nat.add(1n+hi, 0n))
      %Equal.sym(Maybe<&2, Ad.Cls>, Ad.pick.go(rr, 0n, 1n+hi, wb1), None{}, ad.pick_none_hi(rr, hi, wb1)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(1n+hi, 0n, 0n)) == True{} : Bool}
      {==}
    case False{} True{}:
      %Equal.sym(Nat, Nat.add(hi, 0n), hi, ad.add_zero(hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, _), 0n, hi, wb1))), Ad.calm.n(hi, 0n, 0n)) == True{} : Bool}
      %Equal.sym(Bool, Ad.room(l, hi), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 0n, hi, wb1))), Ad.calm.n(hi, 0n, 0n)) == True{} : Bool}
      {==}
    case False{} False{}:
      %Equal.sym(Nat, Nat.add(hi, 0n), hi, ad.add_zero(hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, _), 1n, hi, wb1))), Ad.calm.n(hi, 1n, 0n)) == True{} : Bool}
      %Equal.sym(Bool, Ad.room(l, hi), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 1n, hi, wb1))), Ad.calm.n(hi, 1n, 0n)) == True{} : Bool}
      {==}

def ad.adm_ia1(+l: Ad.Lim, +hi: Nat, +w: Nat, +wb1: Nat, u: Bool, er: {Ad.room(l, Nat.add(hi, 0n)) == False{} : Bool}) -> {ad.ok.n(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(False{}, u)}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(False{}, u)}), 1n+w), 0n, wb1) == True{} : Bool}:
  match u:
    case True{}:
      %Equal.sym(Bool, Ad.room(l, Nat.add(hi, 0n)), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 1n+w, hi, wb1))), Ad.calm.n(hi, 1n+w, 0n)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Ad.room(l, Nat.add(hi, 0n)), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 2n+w, hi, wb1))), Ad.calm.n(hi, 2n+w, 0n)) == True{} : Bool}
      {==}

def ad.room0(+l: Ad.Lim, +hi: Nat, +w: Nat, +hb: Nat, +wb: Nat, +h: {ad.ok.n(l, hi, 1n+w, hb, wb) == True{} : Bool}) -> {Ad.room(l, Nat.add(hi, 0n)) == False{} : Bool}:
  +cn = Ad.calm.n(hi, 1n+w, hb)
  %ad.calm_hb0(hi, w, hb, ad.and_r(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(Ad.room(l, Nat.add(hi, hb)), 1n+w, hi, wb))), cn, h)) : {Ad.room(l, Nat.add(hi, _)) == False{} : Bool}
  ad.ok_room(Ad.room(l, Nat.add(hi, hb)), w, hi, wb, cn, h)

def ad.adm_ia(+l: Ad.Lim, +q: Nat, +wi: Nat, +hi: Nat, +hb: Nat, +wb: Nat, +wb1: Nat, +h: {ad.ok.n(l, hi, wi, hb, wb) == True{} : Bool}) -> {ad.ok.n(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))}), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))}), wi), 0n, wb1) == True{} : Bool}:
  match wi:
    case 0n:
      ad.adm_ia0(l, hi, wb1, Ad.room(l, hi), Ad.le(q, 0n), {==})
    case 1n+w:
      ad.adm_ia1(l, hi, w, wb1, Ad.le(q, 1n+w), ad.room0(l, hi, w, hb, wb, h))

def ad.adm_ia_ok(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +h: {ad.ok(l, ts) == True{} : Bool}) -> {ad.ok(l, Ad.admit.ia(l, q, ts)) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
  +st = Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))
  +x = {Ad.Tk{Ad.Ia{}, st} : Ad.Tk}
  +t1 = Ad.preempt(ts)
  +t2 = List.append(&2, Ad.Tk, t1, [x])
  ad.ok.tr(l, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), hi), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, x), wi), 0n, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), hi), ad.app_pre(Ad.Holding{}, ts, x)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, x), wi), ad.app_pre(Ad.Waiting{}, ts, x)), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), 0n, Equal.trans(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t1), 0n, ad.app_off(Ad.Holding{}, Ad.Bg{}, t1, x, ad.and_f(Ad.Mode.of(Ad.Holding{}, st))), ad.pre_hb(ts))), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), ad.app_off(Ad.Waiting{}, Ad.Bg{}, t1, x, ad.and_f(Ad.Mode.of(Ad.Waiting{}, st)))), ad.adm_ia(l, q, wi, hi, hb, wb, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t1), h))

# a background admit: a slot only when no request holds one
# interactively or waits
def ad.adm_bg0(+l: Ad.Lim, +hb: Nat, r: Bool, er: {Ad.room(l, hb) == r : Bool}) -> {ad.ok.n(l, 0n, 0n, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(r)}), hb), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(r)}), 0n)) == True{} : Bool}:
  match r:
    case True{}:
      +rr = Ad.room(l, 1n+hb)
      %Equal.sym(Maybe<&2, Ad.Cls>, Ad.pick.go(rr, 0n, 0n, 0n), None{}, ad.pick_none0(rr, 0n)) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, _)), Ad.calm.n(0n, 0n, 1n+hb)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Ad.room(l, hb), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(_, 0n, 0n, 1n))), Ad.calm.n(0n, 0n, hb)) == True{} : Bool}
      ad.or_t(Ad.isz(hb))

def ad.adm_bg(+l: Ad.Lim, +hi: Nat, +wi: Nat, +wb: Nat, +hb: Nat, h: {ad.ok.n(l, hi, wi, hb, wb) == True{} : Bool}) -> {ad.ok.n(l, hi, wi, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))}), hb), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))}), wb)) == True{} : Bool}:
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

def ad.adm_bg_ok(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, h: {ad.ok(l, ts) == True{} : Bool}) -> {ad.ok(l, Ad.admit.bg(l, ts)) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
  +st = Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))
  +y = {Ad.Tk{Ad.Bg{}, st} : Ad.Tk}
  +t2 = List.append(&2, Ad.Tk, ts, [y])
  ad.ok.tr(l, hi, wi, Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, y), hb), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, y), wb), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), hi, ad.app_off(Ad.Holding{}, Ad.Ia{}, ts, y, ad.and_f(Ad.Mode.of(Ad.Holding{}, st)))), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), wi, ad.app_off(Ad.Waiting{}, Ad.Ia{}, ts, y, ad.and_f(Ad.Mode.of(Ad.Waiting{}, st)))), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Bg{}, y), hb), ad.cnt_app(Ad.Holding{}, Ad.Bg{}, ts, y)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.bit(Ad.hit(Ad.Waiting{}, Ad.Bg{}, y), wb), ad.cnt_app(Ad.Waiting{}, Ad.Bg{}, ts, y)), ad.adm_bg(l, hi, wi, wb, hb, h))

# the ticket ops, by the ticket's status
def ad.col_ok(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, h: {ad.ok(l, ts) == True{} : Bool}) -> {ad.okS(Ad.collect.at(mb, l, q, ts, k)) == True{} : Bool}:
  match mb:
    case None{}:
      h
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      h
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      +t2 = Ad.put(ts, k, Ad.Held{})
      ad.ok.tr(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), ad.col_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), ad.col_cnt(Ad.Waiting{}, Ad.Ia{}, ts, k, c, e)), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), ad.col_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), ad.col_cnt(Ad.Waiting{}, Ad.Bg{}, ts, k, c, e)), h)
    case Some{Ad.Tk{c, Ad.Held{}}}:
      h
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      h
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      h

def ad.rel_ok(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, +h: {ad.ok(l, ts) == True{} : Bool}) -> {ad.okS(Ad.release.at(mb, l, q, ts, k)) == True{} : Bool}:
  match mb:
    case None{}:
      h
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      h
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      h
    case Some{Ad.Tk{+c, Ad.Held{}}}:
      ad.end_grant(l, ts, k, c, Ad.Held{}, e, ad.calm_of(l, ts, h))
    case Some{Ad.Tk{+c, Ad.Preempted{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      ad.ok.tr(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, Ad.Preempted{}, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), ad.end_cnt(Ad.Waiting{}, Ad.Ia{}, ts, k, c, Ad.Preempted{}, e)), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, Ad.Preempted{}, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), ad.end_cnt(Ad.Waiting{}, Ad.Bg{}, ts, k, c, Ad.Preempted{}, e)), h)
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      h

def ad.lea_ok(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, +h: {ad.ok(l, ts) == True{} : Bool}) -> {ad.okS(Ad.leave.at(mb, l, q, ts, k)) == True{} : Bool}:
  match mb:
    case None{}:
      h
    case Some{Ad.Tk{+c, Ad.Queued{}}}:
      ad.end_grant(l, ts, k, c, Ad.Queued{}, e, ad.calm_of(l, ts, h))
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      ad.end_grant(l, ts, k, c, Ad.Granted{}, e, ad.calm_of(l, ts, h))
    case Some{Ad.Tk{c, Ad.Held{}}}:
      h
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      h
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      h

def ad.step_ok(s: Ad.St, o: Ad.Op, +h: {ad.okS(s) == True{} : Bool}) -> {ad.okS(Ad.step(s, o)) == True{} : Bool}:
  match s:
    case Ad.St{+l, +q, +ts}:
      match o:
        case Ad.Admit{Ad.Ia{}}:
          ad.adm_ia_ok(l, q, ts, h)
        case Ad.Admit{Ad.Bg{}}:
          ad.adm_bg_ok(l, ts, h)
        case Ad.Collect{+k}:
          ad.col_ok(Ad.get(ts, k), l, q, ts, k, {==}, h)
        case Ad.Release{+k}:
          ad.rel_ok(Ad.get(ts, k), l, q, ts, k, {==}, h)
        case Ad.Leave{+k}:
          ad.lea_ok(Ad.get(ts, k), l, q, ts, k, {==}, h)
        case Ad.Limit{+l2, q2}:
          ad.grant_ok(Ad.waits(ts), Ad.pick(l2, ts), l2, ts, {==}, ad.le_refl(Ad.waits(ts)), ad.calm_of(l, ts, h))

def ad.run_ok(os: List<&2, Ad.Op>, +s: Ad.St, h: {ad.okS(s) == True{} : Bool}) -> {ad.okS(Ad.run(os, s)) == True{} : Bool}:
  match os:
    case Nil{}:
      h
    case +o <> r:
      ad.run_ok(r, Ad.step(s, o), ad.step_ok(s, o, h))

def ad.new_ok(l: Ad.Lim, -q: Nat) -> {ad.okS(Ad.St.new(l, q)) == True{} : Bool}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      {==}

def ad.end_mark(t: List<&2, Ad.Tk>, +c: Ad.Cls, k: Nat, e: {Ad.ended(Ad.get(t, k)) == True{} : Bool}) -> {Ad.ended(Ad.get(Ad.mark(c, t), k)) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs:
        case Ad.Ia{} Ad.Queued{}:
          match c k:
            case Ad.Ia{} 0n:
              ad.absurd({Ad.ended(Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}}) == True{} : Bool}, e)
            case Ad.Ia{} 1n+p:
              e
            case Ad.Bg{} 0n:
              e
            case Ad.Bg{} 1n+p:
              ad.end_mark(r, Ad.Bg{}, p, e)
        case Ad.Bg{} Ad.Queued{}:
          match c k:
            case Ad.Bg{} 0n:
              ad.absurd({Ad.ended(Some{Ad.Tk{Ad.Bg{}, Ad.Granted{}}}) == True{} : Bool}, e)
            case Ad.Bg{} 1n+p:
              e
            case Ad.Ia{} 0n:
              e
            case Ad.Ia{} 1n+p:
              ad.end_mark(r, Ad.Ia{}, p, e)
        case _ Ad.Granted{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ Ad.Held{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ Ad.Preempted{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ Ad.Ended{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)

def ad.end_grant_k(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +k: Nat, e: {Ad.ended(Ad.get(t, k)) == True{} : Bool}) -> {Ad.ended(Ad.get(Ad.grant.go(n, d, l, t), k)) == True{} : Bool}:
  match n d:
    case 0n _:
      e
    case 1n+f None{}:
      e
    case 1n+f Some{+c}:
      ad.end_grant_k(f, Ad.pick(l, Ad.mark(c, t)), l, Ad.mark(c, t), k, ad.end_mark(t, c, k, e))

# Slots held stay within the limit
# --------------------------------

def ad.le_trans(a: Nat, b: Nat, c: Nat, ab: {Ad.le(a, b) == True{} : Bool}, bc: {Ad.le(b, c) == True{} : Bool}) -> {Ad.le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      {==}
    case 1n+x 0n _:
      ad.absurd({Ad.le(1n+x, c) == True{} : Bool}, ab)
    case 1n+x 1n+y 0n:
      ad.absurd({Ad.le(1n+x, 0n) == True{} : Bool}, bc)
    case 1n+x 1n+y 1n+z:
      ad.le_trans(x, y, z, ab, bc)

def ad.add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ad.add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def ad.isg(m: Maybe<&2, Ad.Tk>) -> Bool:
  match m:
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      True{}
    case _:
      False{}

def ad.isg_at(-ts: List<&2, Ad.Tk>, -k: Nat, -mb: Maybe<&2, Ad.Tk>, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, f: {ad.isg(mb) == True{} : Bool}) -> {ad.isg(Ad.get(ts, k)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, k), mb, ej) : {ad.isg(_) == True{} : Bool}
  f

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
          ad.absurd({Ad.le(1n+a, 1n) == True{} : Bool}, e)
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

def aw.isz_bit(b: Bool, -n: Nat, e: {Ad.isz(n) == False{} : Bool}) -> {Ad.isz(Ad.bit(b, n)) == False{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      {==}

# What w waits for
# ----------------

def aw.pot0(t: List<&2, Ad.Tk>) -> {Ad.pot(t, 0n) == Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case h <> r:
      {==}

def aw.wait0(h: Ad.Tk, -r: List<&2, Ad.Tk>, e: {Ad.waits.ia(Some{h}) == True{} : Bool}) -> {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, h <> r)) == False{} : Bool}:
  match h:
    case Ad.Tk{Ad.Ia{}, Ad.Queued{}}:
      {==}
    case Ad.Tk{Ad.Ia{}, Ad.Granted{}}:
      ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Granted{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Ia{}, Ad.Held{}}:
      ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Held{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Ia{}, Ad.Preempted{}}:
      ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Preempted{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Ia{}, Ad.Ended{}}:
      ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Ended{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Bg{}, s}:
      ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, s} <> r)) == False{} : Bool}, e)

# an interactive waiter is counted
def aw.wait_cnt(t: List<&2, Ad.Tk>, w: Nat, e: {Ad.waits.ia(Ad.get(t, w)) == True{} : Bool}) -> {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)) == False{} : Bool}:
  match t w:
    case Nil{} _:
      ad.absurd({Ad.isz(0n) == False{} : Bool}, e)
    case +h <> +r 0n:
      aw.wait0(h, r, e)
    case +h <> +r 1n+p:
      aw.isz_bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, h), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, r), aw.wait_cnt(r, p, e))

# What each change does to it
# ---------------------------

def aw.pot_pre(t: List<&2, Ad.Tk>, +w: Nat) -> {Ad.pot(Ad.preempt(t), w) == Ad.pot(t, w) : Nat}:
  match t w:
    case Nil{} _:
      {==}
    case +h <> +r 0n:
      ad.pre_ia(Ad.Holding{}, h <> r)
    case +h <> +r 1n+p:
      +hh = Ad.hit(Ad.Holding{}, Ad.Ia{}, h)
      +hw = Ad.hit(Ad.Waiting{}, Ad.Ia{}, h)
      +rhs = Ad.bit(Bool.or(hh, hw), Ad.pot(r, p))
      %Equal.sym(Bool, Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk.preempt(h)), hh, ad.hit_pre(Ad.Holding{}, h)) : {Ad.bit(Bool.or(_, Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk.preempt(h))), Ad.pot(Ad.preempt(r), p)) == rhs : Nat}
      %Equal.sym(Bool, Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk.preempt(h)), hw, ad.hit_pre(Ad.Waiting{}, h)) : {Ad.bit(Bool.or(hh, _), Ad.pot(Ad.preempt(r), p)) == rhs : Nat}
      %Equal.sym(Nat, Ad.pot(Ad.preempt(r), p), Ad.pot(r, p), aw.pot_pre(r, p)) : {Ad.bit(Bool.or(hh, hw), _) == rhs : Nat}
      {==}

def aw.wait_pre1(t: Ad.Tk) -> {Ad.waits.ia(Some{Ad.Tk.preempt(t)}) == Ad.waits.ia(Some{t}) : Bool}:
  match t:
    case Ad.Tk{Ad.Ia{}, s}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Queued{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Granted{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Held{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Preempted{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Ended{}}:
      {==}

def aw.wait_pre(t: List<&2, Ad.Tk>, w: Nat) -> {Ad.waits.ia(Ad.get(Ad.preempt(t), w)) == Ad.waits.ia(Ad.get(t, w)) : Bool}:
  match t w:
    case Nil{} _:
      {==}
    case +h <> +r 0n:
      aw.wait_pre1(h)
    case +h <> +r 1n+p:
      aw.wait_pre(r, p)

# a new ticket comes after w
def aw.pot_app(t: List<&2, Ad.Tk>, +x: Ad.Tk, +w: Nat, ws: {Ad.waits.ia(Ad.get(t, w)) == True{} : Bool}) -> {Ad.pot(List.append(&2, Ad.Tk, t, [x]), w) == Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), Ad.pot(t, w)) : Nat}:
  match t w:
    case Nil{} _:
      ad.absurd({Ad.pot([x], w) == Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), 0n) : Nat}, ws)
    case +h <> +r 0n:
      ad.cnt_app(Ad.Holding{}, Ad.Ia{}, h <> r, x)
    case +h <> +r 1n+p:
      +b = Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, h), Ad.hit(Ad.Waiting{}, Ad.Ia{}, h))
      +hx = Ad.hit(Ad.Holding{}, Ad.Ia{}, x)
      %Equal.sym(Nat, Ad.pot(List.append(&2, Ad.Tk, r, [x]), p), Ad.bit(hx, Ad.pot(r, p)), aw.pot_app(r, x, p, ws)) : {Ad.bit(b, _) == Ad.bit(hx, Ad.bit(b, Ad.pot(r, p))) : Nat}
      ad.bit_comm(b, hx, Ad.pot(r, p))

def aw.end0(+r: List<&2, Ad.Tk>, +q: Nat, -a: Bool, ih: {Ad.le(Ad.bit(a, Ad.pot(Ad.put(r, q, Ad.Ended{}), 0n)), Ad.pot(r, 0n)) == True{} : Bool}) -> {Ad.le(Ad.bit(a, Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(r, q, Ad.Ended{}))), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r)) == True{} : Bool}:
  %aw.pot0(Ad.put(r, q, Ad.Ended{})) : {Ad.le(Ad.bit(a, _), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r)) == True{} : Bool}
  %aw.pot0(r) : {Ad.le(Ad.bit(a, Ad.pot(Ad.put(r, q, Ad.Ended{}), 0n)), _) == True{} : Bool}
  ih

# a ticket that ends drops what it weighed (an interactive slot at
# least, if it held one)
def aw.pot_end(t: List<&2, Ad.Tk>, +k: Nat, +w: Nat) -> {Ad.le(Ad.bit(ad.at(Ad.Holding{}, Ad.Ia{}, Ad.get(t, k)), Ad.pot(Ad.put(t, k, Ad.Ended{}), w)), Ad.pot(t, w)) == True{} : Bool}:
  match t k w:
    case Nil{} _ _:
      {==}
    case Ad.Tk{+c1, +s1} <> +r 0n 0n:
      ad.le_refl(Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{c1, s1}), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r)))
    case Ad.Tk{+c1, +s1} <> +r 0n 1n+p:
      aw.bit_or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{c1, s1}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{c1, s1}), Ad.pot(r, p))
    case Ad.Tk{+c1, +s1} <> +r 1n+q 0n:
      +hh = Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{c1, s1})
      +a = ad.at(Ad.Holding{}, Ad.Ia{}, Ad.get(r, q))
      +x = Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.put(r, q, Ad.Ended{}))
      %ad.bit_comm(hh, a, x) : {Ad.le(_, Ad.bit(hh, Ad.cnt(Ad.Holding{}, Ad.Ia{}, r))) == True{} : Bool}
      aw.bit_mono(hh, Ad.bit(a, x), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.end0(r, q, a, aw.pot_end(r, q, 0n)))
    case Ad.Tk{+c1, +s1} <> +r 1n+q 1n+p:
      +a = ad.at(Ad.Holding{}, Ad.Ia{}, Ad.get(r, q))
      +b = Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{c1, s1}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{c1, s1}))
      %ad.bit_comm(b, a, Ad.pot(Ad.put(r, q, Ad.Ended{}), p)) : {Ad.le(_, Ad.bit(b, Ad.pot(r, p))) == True{} : Bool}
      aw.bit_mono(b, Ad.bit(a, Ad.pot(Ad.put(r, q, Ad.Ended{}), p)), Ad.pot(r, p), aw.pot_end(r, q, p))

def aw.c_of(+x: List<&2, Ad.Tk>, +y: List<&2, Ad.Tk>, e: {Ad.pot(x, 0n) == Ad.pot(y, 0n) : Nat}) -> {Ad.cnt(Ad.Holding{}, Ad.Ia{}, x) == Ad.cnt(Ad.Holding{}, Ad.Ia{}, y) : Nat}:
  %aw.pot0(x) : {_ == Ad.cnt(Ad.Holding{}, Ad.Ia{}, y) : Nat}
  %aw.pot0(y) : {Ad.pot(x, 0n) == _ : Nat}
  e

def aw.col0(+c1: Ad.Cls, s1: Ad.Sts, -r: List<&2, Ad.Tk>, w: Nat, g: {ad.isg(Some{Ad.Tk{c1, s1}}) == True{} : Bool}) -> {Ad.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) == Ad.pot(Ad.Tk{c1, s1} <> r, w) : Nat}:
  match s1:
    case Ad.Granted{}:
      match w:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Ad.Queued{}:
      ad.absurd({Ad.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) == Ad.pot(Ad.Tk{c1, Ad.Queued{}} <> r, w) : Nat}, g)
    case Ad.Held{}:
      ad.absurd({Ad.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) == Ad.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) : Nat}, g)
    case Ad.Preempted{}:
      ad.absurd({Ad.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) == Ad.pot(Ad.Tk{c1, Ad.Preempted{}} <> r, w) : Nat}, g)
    case Ad.Ended{}:
      ad.absurd({Ad.pot(Ad.Tk{c1, Ad.Held{}} <> r, w) == Ad.pot(Ad.Tk{c1, Ad.Ended{}} <> r, w) : Nat}, g)

# collecting a grant changes nothing w waits for
def aw.pot_col(t: List<&2, Ad.Tk>, +k: Nat, +w: Nat, +g: {ad.isg(Ad.get(t, k)) == True{} : Bool}) -> {Ad.pot(Ad.put(t, k, Ad.Held{}), w) == Ad.pot(t, w) : Nat}:
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
      Equal.cong(Nat, Nat, y => Ad.bit(b, y), Ad.pot(Ad.put(r, q, Ad.Held{}), p), Ad.pot(r, p), aw.pot_col(r, q, p, g))

# a grant never makes a ticket wait
def aw.wait_mark(t: List<&2, Ad.Tk>, +c: Ad.Cls, +w: Nat, e: {Ad.waits.ia(Ad.get(Ad.mark(c, t), w)) == True{} : Bool}) -> {Ad.waits.ia(Ad.get(t, w)) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs:
        case Ad.Ia{} Ad.Queued{}:
          match c w:
            case Ad.Ia{} 0n:
              ad.absurd({Ad.waits.ia(Some{Ad.Tk{Ad.Ia{}, Ad.Queued{}}}) == True{} : Bool}, e)
            case Ad.Ia{} 1n+p:
              e
            case Ad.Bg{} 0n:
              {==}
            case Ad.Bg{} 1n+p:
              aw.wait_mark(r, Ad.Bg{}, p, e)
        case Ad.Bg{} Ad.Queued{}:
          match c w:
            case Ad.Bg{} 0n:
              ad.absurd({Ad.waits.ia(Some{Ad.Tk{Ad.Bg{}, Ad.Queued{}}}) == True{} : Bool}, e)
            case Ad.Bg{} 1n+p:
              e
            case Ad.Ia{} 0n:
              e
            case Ad.Ia{} 1n+p:
              aw.wait_mark(r, Ad.Ia{}, p, e)
        case _ Ad.Granted{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)
        case _ Ad.Held{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)
        case _ Ad.Preempted{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)
        case _ Ad.Ended{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)

def aw.wait_grant(+n: Nat, +d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +w: Nat, e: {Ad.waits.ia(Ad.get(Ad.grant.go(n, d, l, t), w)) == True{} : Bool}) -> {Ad.waits.ia(Ad.get(t, w)) == True{} : Bool}:
  match n d:
    case 0n _:
      e
    case 1n+f None{}:
      e
    case 1n+f Some{+c}:
      aw.wait_mark(t, c, w, aw.wait_grant(f, Ad.pick(l, Ad.mark(c, t)), l, Ad.mark(c, t), w, e))

# an interactive grant while w waits goes to a waiter ahead of it: it
# moves from waiting to holding, which w waits for alike
def aw.pot_mark_ia(t: List<&2, Ad.Tk>, +w: Nat, +e: {Ad.waits.ia(Ad.get(Ad.mark(Ad.Ia{}, t), w)) == True{} : Bool}) -> {Ad.pot(Ad.mark(Ad.Ia{}, t), w) == Ad.pot(t, w) : Nat}:
  match t:
    case Nil{}:
      {==}
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs w:
        case Ad.Ia{} Ad.Queued{} 0n:
          ad.absurd({Ad.pot(Ad.Tk{Ad.Ia{}, Ad.Granted{}} <> r, 0n) == Ad.pot(Ad.Tk{Ad.Ia{}, Ad.Queued{}} <> r, 0n) : Nat}, e)
        case Ad.Ia{} Ad.Queued{} 1n+p:
          {==}
        case Ad.Ia{} Ad.Granted{} 0n:
          ad.absurd({Ad.pot(Ad.Tk{Ad.Ia{}, Ad.Granted{}} <> Ad.mark(Ad.Ia{}, r), 0n) == Ad.pot(Ad.Tk{Ad.Ia{}, Ad.Granted{}} <> r, 0n) : Nat}, e)
        case Ad.Ia{} Ad.Granted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Granted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Granted{}})), y), Ad.pot(Ad.mark(Ad.Ia{}, r), p), Ad.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Ia{} Ad.Held{} 0n:
          ad.absurd({Ad.pot(Ad.Tk{Ad.Ia{}, Ad.Held{}} <> Ad.mark(Ad.Ia{}, r), 0n) == Ad.pot(Ad.Tk{Ad.Ia{}, Ad.Held{}} <> r, 0n) : Nat}, e)
        case Ad.Ia{} Ad.Held{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Held{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Held{}})), y), Ad.pot(Ad.mark(Ad.Ia{}, r), p), Ad.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Ia{} Ad.Preempted{} 0n:
          ad.absurd({Ad.pot(Ad.Tk{Ad.Ia{}, Ad.Preempted{}} <> Ad.mark(Ad.Ia{}, r), 0n) == Ad.pot(Ad.Tk{Ad.Ia{}, Ad.Preempted{}} <> r, 0n) : Nat}, e)
        case Ad.Ia{} Ad.Preempted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Preempted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Preempted{}})), y), Ad.pot(Ad.mark(Ad.Ia{}, r), p), Ad.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Ia{} Ad.Ended{} 0n:
          ad.absurd({Ad.pot(Ad.Tk{Ad.Ia{}, Ad.Ended{}} <> Ad.mark(Ad.Ia{}, r), 0n) == Ad.pot(Ad.Tk{Ad.Ia{}, Ad.Ended{}} <> r, 0n) : Nat}, e)
        case Ad.Ia{} Ad.Ended{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Ended{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Ended{}})), y), Ad.pot(Ad.mark(Ad.Ia{}, r), p), Ad.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Bg{} Ad.Queued{} 0n:
          ad.absurd({Ad.pot(Ad.Tk{Ad.Bg{}, Ad.Queued{}} <> Ad.mark(Ad.Ia{}, r), 0n) == Ad.pot(Ad.Tk{Ad.Bg{}, Ad.Queued{}} <> r, 0n) : Nat}, e)
        case Ad.Bg{} Ad.Queued{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Queued{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Queued{}})), y), Ad.pot(Ad.mark(Ad.Ia{}, r), p), Ad.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Bg{} Ad.Granted{} 0n:
          ad.absurd({Ad.pot(Ad.Tk{Ad.Bg{}, Ad.Granted{}} <> Ad.mark(Ad.Ia{}, r), 0n) == Ad.pot(Ad.Tk{Ad.Bg{}, Ad.Granted{}} <> r, 0n) : Nat}, e)
        case Ad.Bg{} Ad.Granted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Granted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Granted{}})), y), Ad.pot(Ad.mark(Ad.Ia{}, r), p), Ad.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Bg{} Ad.Held{} 0n:
          ad.absurd({Ad.pot(Ad.Tk{Ad.Bg{}, Ad.Held{}} <> Ad.mark(Ad.Ia{}, r), 0n) == Ad.pot(Ad.Tk{Ad.Bg{}, Ad.Held{}} <> r, 0n) : Nat}, e)
        case Ad.Bg{} Ad.Held{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Held{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Held{}})), y), Ad.pot(Ad.mark(Ad.Ia{}, r), p), Ad.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Bg{} Ad.Preempted{} 0n:
          ad.absurd({Ad.pot(Ad.Tk{Ad.Bg{}, Ad.Preempted{}} <> Ad.mark(Ad.Ia{}, r), 0n) == Ad.pot(Ad.Tk{Ad.Bg{}, Ad.Preempted{}} <> r, 0n) : Nat}, e)
        case Ad.Bg{} Ad.Preempted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Preempted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Preempted{}})), y), Ad.pot(Ad.mark(Ad.Ia{}, r), p), Ad.pot(r, p), aw.pot_mark_ia(r, p, e))
        case Ad.Bg{} Ad.Ended{} 0n:
          ad.absurd({Ad.pot(Ad.Tk{Ad.Bg{}, Ad.Ended{}} <> Ad.mark(Ad.Ia{}, r), 0n) == Ad.pot(Ad.Tk{Ad.Bg{}, Ad.Ended{}} <> r, 0n) : Nat}, e)
        case Ad.Bg{} Ad.Ended{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Ended{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, Ad.Ended{}})), y), Ad.pot(Ad.mark(Ad.Ia{}, r), p), Ad.pot(r, p), aw.pot_mark_ia(r, p, e))

# a background grant changes nothing w waits for
def aw.pot_mark_bg(t: List<&2, Ad.Tk>, +w: Nat) -> {Ad.pot(Ad.mark(Ad.Bg{}, t), w) == Ad.pot(t, w) : Nat}:
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
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Queued{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Queued{}})), y), Ad.pot(Ad.mark(Ad.Bg{}, r), p), Ad.pot(r, p), aw.pot_mark_bg(r, p))
        case _ Ad.Granted{} 0n:
          Equal.cong(Nat, Nat, y => Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Granted{}}), y), Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.mark(Ad.Bg{}, r)), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.c_of(Ad.mark(Ad.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ Ad.Granted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Granted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Granted{}})), y), Ad.pot(Ad.mark(Ad.Bg{}, r), p), Ad.pot(r, p), aw.pot_mark_bg(r, p))
        case _ Ad.Held{} 0n:
          Equal.cong(Nat, Nat, y => Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Held{}}), y), Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.mark(Ad.Bg{}, r)), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.c_of(Ad.mark(Ad.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ Ad.Held{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Held{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Held{}})), y), Ad.pot(Ad.mark(Ad.Bg{}, r), p), Ad.pot(r, p), aw.pot_mark_bg(r, p))
        case _ Ad.Preempted{} 0n:
          Equal.cong(Nat, Nat, y => Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Preempted{}}), y), Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.mark(Ad.Bg{}, r)), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.c_of(Ad.mark(Ad.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ Ad.Preempted{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Preempted{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Preempted{}})), y), Ad.pot(Ad.mark(Ad.Bg{}, r), p), Ad.pot(r, p), aw.pot_mark_bg(r, p))
        case _ Ad.Ended{} 0n:
          Equal.cong(Nat, Nat, y => Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Ended{}}), y), Ad.cnt(Ad.Holding{}, Ad.Ia{}, Ad.mark(Ad.Bg{}, r)), Ad.cnt(Ad.Holding{}, Ad.Ia{}, r), aw.c_of(Ad.mark(Ad.Bg{}, r), r, aw.pot_mark_bg(r, 0n)))
        case _ Ad.Ended{} 1n+p:
          Equal.cong(Nat, Nat, y => Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, Ad.Tk{hc, Ad.Ended{}}), Ad.hit(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{hc, Ad.Ended{}})), y), Ad.pot(Ad.mark(Ad.Bg{}, r), p), Ad.pot(r, p), aw.pot_mark_bg(r, p))

def aw.pot_grant(+n: Nat, +d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +w: Nat, +e: {Ad.waits.ia(Ad.get(Ad.grant.go(n, d, l, t), w)) == True{} : Bool}) -> {Ad.pot(Ad.grant.go(n, d, l, t), w) == Ad.pot(t, w) : Nat}:
  match n d:
    case 0n _:
      {==}
    case 1n+f None{}:
      {==}
    case 1n+f Some{Ad.Ia{}}:
      +t2 = Ad.mark(Ad.Ia{}, t)
      Equal.trans(Nat, Ad.pot(Ad.grant.go(f, Ad.pick(l, t2), l, t2), w), Ad.pot(t2, w), Ad.pot(t, w), aw.pot_grant(f, Ad.pick(l, t2), l, t2, w, e), aw.pot_mark_ia(t, w, aw.wait_grant(f, Ad.pick(l, t2), l, t2, w, e)))
    case 1n+f Some{Ad.Bg{}}:
      +t2 = Ad.mark(Ad.Bg{}, t)
      Equal.trans(Nat, Ad.pot(Ad.grant.go(f, Ad.pick(l, t2), l, t2), w), Ad.pot(t2, w), Ad.pot(t, w), aw.pot_grant(f, Ad.pick(l, t2), l, t2, w, e), aw.pot_mark_bg(t, w))

# One op
# ------

def aw.ia_new(-r: Bool, u: Bool, +p: Nat) -> {Ad.le(Ad.bit(Bool.and(Ad.Mode.of(Ad.Holding{}, Ad.admit.ia.st(Bool.and(False{}, r), u)), True{}), p), p) == True{} : Bool}:
  match u:
    case True{}:
      ad.le_refl(p)
    case False{}:
      ad.le_refl(p)

# a new interactive request waits behind w
def aw.st_ia(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +w: Nat, +ws: {Ad.waits.ia(Ad.get(ts, w)) == True{} : Bool}) -> {Ad.le(Ad.pot(Ad.admit.ia(l, q, ts), w), Ad.pot(ts, w)) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +st = Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))
  +x = {Ad.Tk{Ad.Ia{}, st} : Ad.Tk}
  +t1 = Ad.preempt(ts)
  +p = Ad.pot(ts, w)
  +ws1 = Equal.trans(Bool, Ad.waits.ia(Ad.get(t1, w)), Ad.waits.ia(Ad.get(ts, w)), True{}, aw.wait_pre(ts, w), ws)
  %Equal.sym(Nat, Ad.pot(List.append(&2, Ad.Tk, t1, [x]), w), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), Ad.pot(t1, w)), aw.pot_app(t1, x, w, ws1)) : {Ad.le(_, p) == True{} : Bool}
  %Equal.sym(Nat, Ad.pot(t1, w), p, aw.pot_pre(ts, w)) : {Ad.le(Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), _), p) == True{} : Bool}
  %Equal.sym(Bool, Ad.isz(wi), False{}, aw.wait_cnt(ts, w, ws)) : {Ad.le(Ad.bit(Bool.and(Ad.Mode.of(Ad.Holding{}, Ad.admit.ia.st(Bool.and(_, Ad.room(l, hi)), Ad.le(q, wi))), True{}), p), p) == True{} : Bool}
  aw.ia_new(Ad.room(l, hi), Ad.le(q, wi), p)

# a new background request changes nothing w waits for
def aw.st_bg(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, +w: Nat, ws: {Ad.waits.ia(Ad.get(ts, w)) == True{} : Bool}) -> {Ad.le(Ad.pot(Ad.admit.bg(l, ts), w), Ad.pot(ts, w)) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
  +st = Ad.admit.bg.st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, Nat.add(hi, hb))))))
  +y = {Ad.Tk{Ad.Bg{}, st} : Ad.Tk}
  +p = Ad.pot(ts, w)
  %Equal.sym(Nat, Ad.pot(List.append(&2, Ad.Tk, ts, [y]), w), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, y), p), aw.pot_app(ts, y, w, ws)) : {Ad.le(_, p) == True{} : Bool}
  %Equal.sym(Bool, Bool.and(Ad.Mode.of(Ad.Holding{}, st), False{}), False{}, ad.and_f(Ad.Mode.of(Ad.Holding{}, st))) : {Ad.le(Ad.bit(_, p), p) == True{} : Bool}
  ad.le_refl(p)

def aw.end_at(+ts: List<&2, Ad.Tk>, +k: Nat, +w: Nat, -mb: Maybe<&2, Ad.Tk>, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}) -> {Ad.le(Ad.bit(ad.at(Ad.Holding{}, Ad.Ia{}, mb), Ad.pot(Ad.put(ts, k, Ad.Ended{}), w)), Ad.pot(ts, w)) == True{} : Bool}:
  %ej : {Ad.le(Ad.bit(ad.at(Ad.Holding{}, Ad.Ia{}, _), Ad.pot(Ad.put(ts, k, Ad.Ended{}), w)), Ad.pot(ts, w)) == True{} : Bool}
  aw.pot_end(ts, k, w)

def aw.col(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +w: Nat, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}) -> {Ad.le(Ad.pot(Ad.St.ts(Ad.collect.at(mb, l, q, ts, k)), w), Ad.pot(ts, w)) == True{} : Bool}:
  match mb:
    case None{}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      %Equal.sym(Nat, Ad.pot(Ad.put(ts, k, Ad.Held{}), w), Ad.pot(ts, w), aw.pot_col(ts, k, w, ad.isg_at(ts, k, Some{Ad.Tk{c, Ad.Granted{}}}, ej, {==}))) : {Ad.le(_, Ad.pot(ts, w)) == True{} : Bool}
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{c, Ad.Held{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      ad.le_refl(Ad.pot(ts, w))

def aw.rel(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +w: Nat, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, wf: {Ad.waits.ia(Ad.get(Ad.St.ts(Ad.release.at(mb, l, q, ts, k)), w)) == True{} : Bool}) -> {Ad.le(Nat.add(Ad.frees.at(mb, True{}), Ad.pot(Ad.St.ts(Ad.release.at(mb, l, q, ts, k)), w)), Ad.pot(ts, w)) == True{} : Bool}:
  match mb:
    case None{}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Queued{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Held{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Ia{}, Ad.Held{}}}, True{}), _), Ad.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Ia{}, Ad.Held{}}}, ej)
    case Some{Ad.Tk{Ad.Ia{}, Ad.Preempted{}}}:
      aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Ia{}, Ad.Preempted{}}}, ej)
    case Some{Ad.Tk{Ad.Ia{}, Ad.Ended{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Queued{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Granted{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Held{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Bg{}, Ad.Held{}}}, True{}), _), Ad.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Bg{}, Ad.Held{}}}, ej)
    case Some{Ad.Tk{Ad.Bg{}, Ad.Preempted{}}}:
      aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Bg{}, Ad.Preempted{}}}, ej)
    case Some{Ad.Tk{Ad.Bg{}, Ad.Ended{}}}:
      ad.le_refl(Ad.pot(ts, w))

def aw.lea(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +w: Nat, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, wf: {Ad.waits.ia(Ad.get(Ad.St.ts(Ad.leave.at(mb, l, q, ts, k)), w)) == True{} : Bool}) -> {Ad.le(Nat.add(Ad.frees.at(mb, False{}), Ad.pot(Ad.St.ts(Ad.leave.at(mb, l, q, ts, k)), w)), Ad.pot(ts, w)) == True{} : Bool}:
  match mb:
    case None{}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Queued{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Ia{}, Ad.Queued{}}}, False{}), _), Ad.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Ia{}, Ad.Queued{}}}, ej)
    case Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}}, False{}), _), Ad.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}}, ej)
    case Some{Ad.Tk{Ad.Ia{}, Ad.Held{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Preempted{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Ended{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Queued{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Bg{}, Ad.Queued{}}}, False{}), _), Ad.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Bg{}, Ad.Queued{}}}, ej)
    case Some{Ad.Tk{Ad.Bg{}, Ad.Granted{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Bg{}, Ad.Granted{}}}, False{}), _), Ad.pot(ts, w)) == True{} : Bool}
      aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Bg{}, Ad.Granted{}}}, ej)
    case Some{Ad.Tk{Ad.Bg{}, Ad.Held{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Preempted{}}}:
      ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Ended{}}}:
      ad.le_refl(Ad.pot(ts, w))

def aw.step(s: Ad.St, o: Ad.Op, +w: Nat, +ws: {Ad.waits.ia(Ad.status(s, w)) == True{} : Bool}, wf: {Ad.waits.ia(Ad.status(Ad.step(s, o), w)) == True{} : Bool}) -> {Ad.le(Nat.add(Ad.frees(s, o), Ad.ahead(Ad.step(s, o), w)), Ad.ahead(s, w)) == True{} : Bool}:
  match s o:
    case Ad.St{+l, +q, +ts} Ad.Admit{Ad.Ia{}}:
      aw.st_ia(l, q, ts, w, ws)
    case Ad.St{+l, +q, +ts} Ad.Admit{Ad.Bg{}}:
      aw.st_bg(l, ts, w, ws)
    case Ad.St{+l, +q, +ts} Ad.Collect{+k}:
      aw.col(Ad.get(ts, k), l, q, ts, k, w, {==})
    case Ad.St{+l, +q, +ts} Ad.Release{+k}:
      aw.rel(Ad.get(ts, k), l, q, ts, k, w, {==}, wf)
    case Ad.St{+l, +q, +ts} Ad.Leave{+k}:
      aw.lea(Ad.get(ts, k), l, q, ts, k, w, {==}, wf)
    case Ad.St{+l, +q, +ts} Ad.Limit{+l2, q2}:
      %Equal.sym(Nat, Ad.pot(Ad.grant(l2, ts), w), Ad.pot(ts, w), aw.pot_grant(Ad.waits(ts), Ad.pick(l2, ts), l2, ts, w, wf)) : {Ad.le(_, Ad.pot(ts, w)) == True{} : Bool}
      ad.le_refl(Ad.pot(ts, w))

# ---- admission_live ----

# proof_admission_live: the live controller (Ad.Live in bend/admission.bend)
# against the model: on any state of the model, an op of the live
# controller on the model's live tickets gives the live tickets of the
# model's op (LAWS.bend admission_live_step). Each part of an op commutes
# with taking the live tickets (`Laws.adl_lives`): a count, a grant, a
# preemption, an admit (a ticket appended, numbered by the length), and a
# ticket found, set or dropped by its number (the numbers of the live
# tickets from the j-th on are at least j).

# Nat
# ---

def al.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %al.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def al.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %al.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def al.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      al.eq_refl(p)

# j is not a number past it
def al.ne_add(+i: Nat, j: Nat) -> {Nat.is_eq(j, 1n+Nat.add(i, j)) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(i, 1n+p), 1n+Nat.add(i, p), al.add_succ(i, p)) : {Nat.is_eq(1n+p, 1n+_) == False{} : Bool}
      al.ne_add(i, p)

def al.ne_add2(+d: Nat, j: Nat) -> {Nat.is_eq(1n+Nat.add(d, j), j) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(d, 1n+p), 1n+Nat.add(d, p), al.add_succ(d, p)) : {Nat.is_eq(1n+_, 1n+p) == False{} : Bool}
      al.ne_add2(d, p)

# Counting
# --------

def al.keep_cnt(s: Ad.Sts, +m: Ad.Mode, +c: Ad.Cls, +j: Nat, +c2: Ad.Cls, +rest: List<&2, Ad.Lv>) -> {Ad.lv.cnt(m, c, Admission.adl_keep(s, j, c2, rest)) == Ad.bit(Ad.hit(m, c, Ad.Tk{c2, s}), Ad.lv.cnt(m, c, rest)) : Nat}:
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
      match m:
        case Ad.Holding{}:
          {==}
        case Ad.Waiting{}:
          {==}

def al.cnt(+m: Ad.Mode, +c: Ad.Cls, ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.cnt(m, c, Admission.adl_lives(ts, j)) == Ad.cnt(m, c, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{+c2, +s} <> +r:
      %Equal.sym(Nat, Ad.lv.cnt(m, c, Admission.adl_keep(s, j, c2, Admission.adl_lives(r, 1n+j))), Ad.bit(Ad.hit(m, c, Ad.Tk{c2, s}), Ad.lv.cnt(m, c, Admission.adl_lives(r, 1n+j))), al.keep_cnt(s, m, c, j, c2, Admission.adl_lives(r, 1n+j))) : {_ == Ad.bit(Ad.hit(m, c, Ad.Tk{c2, s}), Ad.cnt(m, c, r)) : Nat}
      %Equal.sym(Nat, Ad.lv.cnt(m, c, Admission.adl_lives(r, 1n+j)), Ad.cnt(m, c, r), al.cnt(m, c, r, 1n+j)) : {Ad.bit(Ad.hit(m, c, Ad.Tk{c2, s}), _) == Ad.bit(Ad.hit(m, c, Ad.Tk{c2, s}), Ad.cnt(m, c, r)) : Nat}
      {==}

# a count of the live tickets is the count of the model's tickets
def al.cnt_s(+m: Ad.Mode, +c: Ad.Cls, +ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.cnt(m, c, ts) == Ad.lv.cnt(m, c, Admission.adl_lives(ts, j)) : Nat}:
  Equal.sym(Nat, Ad.lv.cnt(m, c, Admission.adl_lives(ts, j)), Ad.cnt(m, c, ts), al.cnt(m, c, ts, j))

def al.held(+ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.held(Admission.adl_lives(ts, j)) == Ad.held(ts) : Nat}:
  %al.cnt_s(Ad.Holding{}, Ad.Ia{}, ts, j) : {Nat.add(_, Ad.lv.cnt(Ad.Holding{}, Ad.Bg{}, Admission.adl_lives(ts, j))) == Ad.held(ts) : Nat}
  %al.cnt_s(Ad.Holding{}, Ad.Bg{}, ts, j) : {Nat.add(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), _) == Ad.held(ts) : Nat}
  {==}

def al.waits(+ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.waits(Admission.adl_lives(ts, j)) == Ad.waits(ts) : Nat}:
  %al.cnt_s(Ad.Waiting{}, Ad.Ia{}, ts, j) : {Nat.add(_, Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, j))) == Ad.waits(ts) : Nat}
  %al.cnt_s(Ad.Waiting{}, Ad.Bg{}, ts, j) : {Nat.add(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), _) == Ad.waits(ts) : Nat}
  {==}

def al.pick(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.pick(l, Admission.adl_lives(ts, j)) == Ad.pick(l, ts) : Maybe<&2, Ad.Cls>}:
  %Equal.sym(Nat, Ad.lv.held(Admission.adl_lives(ts, j)), Ad.held(ts), al.held(ts, j)) : {Ad.pick.go(Ad.room(l, _), Ad.lv.cnt(Ad.Waiting{}, Ad.Ia{}, Admission.adl_lives(ts, j)), Ad.lv.cnt(Ad.Holding{}, Ad.Ia{}, Admission.adl_lives(ts, j)), Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, j))) == Ad.pick(l, ts) : Maybe<&2, Ad.Cls>}
  %al.cnt_s(Ad.Waiting{}, Ad.Ia{}, ts, j) : {Ad.pick.go(Ad.room(l, Ad.held(ts)), _, Ad.lv.cnt(Ad.Holding{}, Ad.Ia{}, Admission.adl_lives(ts, j)), Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, j))) == Ad.pick(l, ts) : Maybe<&2, Ad.Cls>}
  %al.cnt_s(Ad.Holding{}, Ad.Ia{}, ts, j) : {Ad.pick.go(Ad.room(l, Ad.held(ts)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), _, Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, j))) == Ad.pick(l, ts) : Maybe<&2, Ad.Cls>}
  %al.cnt_s(Ad.Waiting{}, Ad.Bg{}, ts, j) : {Ad.pick.go(Ad.room(l, Ad.held(ts)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), _) == Ad.pick(l, ts) : Maybe<&2, Ad.Cls>}
  {==}

# Logic
# -----

def al.Clash(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

# True == False proves anything
def al.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %Equal.sym(Bool, True{}, False{}, e) : al.Clash(_, G)
  Unit{}

# Granting
# --------

def al.mark_at(b: Bool, +c: Ad.Cls, +j: Nat, +c2: Ad.Cls, s: Ad.Sts, +r: List<&2, Ad.Tk>, ne: {Ad.ended(Some{Ad.Tk{c2, s}}) == False{} : Bool}, ih: {Ad.lv.mark(c, Admission.adl_lives(r, 1n+j)) == Admission.adl_lives(Ad.mark(c, r), 1n+j) : List<&2, Ad.Lv>}) -> {Ad.lv.mark.at(b, c, Ad.Lv{j, c2, s}, Admission.adl_lives(r, 1n+j), Ad.lv.mark(c, Admission.adl_lives(r, 1n+j))) == Admission.adl_lives(Ad.mark.at(b, c, Ad.Tk{c2, s}, r, Ad.mark(c, r)), j) : List<&2, Ad.Lv>}:
  match b:
    case True{}:
      {==}
    case False{}:
      match s:
        case Ad.Queued{}:
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c2, Ad.Queued{}} <> x, Ad.lv.mark(c, Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.mark(c, r), 1n+j), ih)
        case Ad.Granted{}:
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c2, Ad.Granted{}} <> x, Ad.lv.mark(c, Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.mark(c, r), 1n+j), ih)
        case Ad.Held{}:
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c2, Ad.Held{}} <> x, Ad.lv.mark(c, Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.mark(c, r), 1n+j), ih)
        case Ad.Preempted{}:
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c2, Ad.Preempted{}} <> x, Ad.lv.mark(c, Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.mark(c, r), 1n+j), ih)
        case Ad.Ended{}:
          al.absurd({Ad.lv.mark.at(False{}, c, Ad.Lv{j, c2, Ad.Ended{}}, Admission.adl_lives(r, 1n+j), Ad.lv.mark(c, Admission.adl_lives(r, 1n+j))) == Admission.adl_lives(Ad.mark.at(False{}, c, Ad.Tk{c2, Ad.Ended{}}, r, Ad.mark(c, r)), j) : List<&2, Ad.Lv>}, ne)

def al.mark(+c: Ad.Cls, ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.mark(c, Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.mark(c, ts), j) : List<&2, Ad.Lv>}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{+c2, s} <> +r:
      match s:
        case Ad.Queued{}:
          al.mark_at(Ad.hit(Ad.Waiting{}, c, Ad.Tk{c2, Ad.Queued{}}), c, j, c2, Ad.Queued{}, r, {==}, al.mark(c, r, 1n+j))
        case Ad.Granted{}:
          al.mark_at(Ad.hit(Ad.Waiting{}, c, Ad.Tk{c2, Ad.Granted{}}), c, j, c2, Ad.Granted{}, r, {==}, al.mark(c, r, 1n+j))
        case Ad.Held{}:
          al.mark_at(Ad.hit(Ad.Waiting{}, c, Ad.Tk{c2, Ad.Held{}}), c, j, c2, Ad.Held{}, r, {==}, al.mark(c, r, 1n+j))
        case Ad.Preempted{}:
          al.mark_at(Ad.hit(Ad.Waiting{}, c, Ad.Tk{c2, Ad.Preempted{}}), c, j, c2, Ad.Preempted{}, r, {==}, al.mark(c, r, 1n+j))
        case Ad.Ended{}:
          al.mark(c, r, 1n+j)

def al.grant_go(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.grant.go(n, d, l, Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.grant.go(n, d, l, ts), j) : List<&2, Ad.Lv>}:
  match n d:
    case 0n _:
      {==}
    case 1n+f None{}:
      {==}
    case 1n+f Some{+c}:
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.mark(c, Admission.adl_lives(ts, j)), Admission.adl_lives(Ad.mark(c, ts), j), al.mark(c, ts, j)) : {Ad.lv.grant.go(f, Ad.lv.pick(l, _), l, _) == Admission.adl_lives(Ad.grant.go(f, Ad.pick(l, Ad.mark(c, ts)), l, Ad.mark(c, ts)), j) : List<&2, Ad.Lv>}
      %Equal.sym(Maybe<&2, Ad.Cls>, Ad.lv.pick(l, Admission.adl_lives(Ad.mark(c, ts), j)), Ad.pick(l, Ad.mark(c, ts)), al.pick(l, Ad.mark(c, ts), j)) : {Ad.lv.grant.go(f, _, l, Admission.adl_lives(Ad.mark(c, ts), j)) == Admission.adl_lives(Ad.grant.go(f, Ad.pick(l, Ad.mark(c, ts)), l, Ad.mark(c, ts)), j) : List<&2, Ad.Lv>}
      al.grant_go(f, Ad.pick(l, Ad.mark(c, ts)), l, Ad.mark(c, ts), j)

def al.grant(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.grant(l, Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.grant(l, ts), j) : List<&2, Ad.Lv>}:
  %Equal.sym(Nat, Ad.lv.waits(Admission.adl_lives(ts, j)), Ad.waits(ts), al.waits(ts, j)) : {Ad.lv.grant.go(_, Ad.lv.pick(l, Admission.adl_lives(ts, j)), l, Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.grant(l, ts), j) : List<&2, Ad.Lv>}
  %Equal.sym(Maybe<&2, Ad.Cls>, Ad.lv.pick(l, Admission.adl_lives(ts, j)), Ad.pick(l, ts), al.pick(l, ts, j)) : {Ad.lv.grant.go(Ad.waits(ts), _, l, Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.grant(l, ts), j) : List<&2, Ad.Lv>}
  al.grant_go(Ad.waits(ts), Ad.pick(l, ts), l, ts, j)

# Preempting
# ----------

def al.preempt(ts: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.preempt(Admission.adl_lives(ts, j)) == Admission.adl_lives(Ad.preempt(ts), j) : List<&2, Ad.Lv>}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{c, s} <> +r:
      match c:
        case Ad.Ia{}:
          match s:
            case Ad.Queued{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Ia{}, Ad.Queued{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Granted{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Ia{}, Ad.Granted{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Held{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Ia{}, Ad.Held{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Preempted{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Ia{}, Ad.Preempted{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Ended{}:
              al.preempt(r, 1n+j)
        case Ad.Bg{}:
          match s:
            case Ad.Queued{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Bg{}, Ad.Queued{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Granted{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Bg{}, Ad.Queued{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Held{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Bg{}, Ad.Preempted{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Preempted{}:
              Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, Ad.Bg{}, Ad.Preempted{}} <> x, Ad.lv.preempt(Admission.adl_lives(r, 1n+j)), Admission.adl_lives(Ad.preempt(r), 1n+j), al.preempt(r, 1n+j))
            case Ad.Ended{}:
              al.preempt(r, 1n+j)

# Lengths
# -------

def al.len_put(ts: List<&2, Ad.Tk>, i: Nat, +x: Ad.Sts) -> {List.length(&2, Ad.Tk, Ad.put(ts, i, x)) == List.length(&2, Ad.Tk, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{c, s} <> r:
      match i:
        case 0n:
          {==}
        case 1n+p:
          Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ad.Tk, Ad.put(r, p, x)), List.length(&2, Ad.Tk, r), al.len_put(r, p, x))

def al.len_mark_at(b: Bool, c: Ad.Cls, h: Ad.Tk, +r: List<&2, Ad.Tk>, -m: List<&2, Ad.Tk>, ih: {List.length(&2, Ad.Tk, m) == List.length(&2, Ad.Tk, r) : Nat}) -> {List.length(&2, Ad.Tk, Ad.mark.at(b, c, h, r, m)) == 1n+List.length(&2, Ad.Tk, r) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ad.Tk, m), List.length(&2, Ad.Tk, r), ih)

def al.len_mark(+c: Ad.Cls, ts: List<&2, Ad.Tk>) -> {List.length(&2, Ad.Tk, Ad.mark(c, ts)) == List.length(&2, Ad.Tk, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case +h <> +r:
      al.len_mark_at(Ad.hit(Ad.Waiting{}, c, h), c, h, r, Ad.mark(c, r), al.len_mark(c, r))

def al.len_grant_go(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +ts: List<&2, Ad.Tk>) -> {List.length(&2, Ad.Tk, Ad.grant.go(n, d, l, ts)) == List.length(&2, Ad.Tk, ts) : Nat}:
  match n d:
    case 0n _:
      {==}
    case 1n+f None{}:
      {==}
    case 1n+f Some{+c}:
      Equal.trans(Nat, List.length(&2, Ad.Tk, Ad.grant.go(f, Ad.pick(l, Ad.mark(c, ts)), l, Ad.mark(c, ts))), List.length(&2, Ad.Tk, Ad.mark(c, ts)), List.length(&2, Ad.Tk, ts), al.len_grant_go(f, Ad.pick(l, Ad.mark(c, ts)), l, Ad.mark(c, ts)), al.len_mark(c, ts))

def al.len_grant(+l: Ad.Lim, +ts: List<&2, Ad.Tk>) -> {List.length(&2, Ad.Tk, Ad.grant(l, ts)) == List.length(&2, Ad.Tk, ts) : Nat}:
  al.len_grant_go(Ad.waits(ts), Ad.pick(l, ts), l, ts)

def al.len_pre(ts: List<&2, Ad.Tk>) -> {List.length(&2, Ad.Tk, Ad.preempt(ts)) == List.length(&2, Ad.Tk, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case h <> r:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ad.Tk, Ad.preempt(r)), List.length(&2, Ad.Tk, r), al.len_pre(r))

def al.len_app1(a: List<&2, Ad.Tk>, -x: Ad.Tk) -> {List.length(&2, Ad.Tk, List.append(&2, Ad.Tk, a, [x])) == 1n+List.length(&2, Ad.Tk, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case h <> r:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ad.Tk, List.append(&2, Ad.Tk, r, [x])), 1n+List.length(&2, Ad.Tk, r), al.len_app1(r, x))

# Admitting
# ---------

def al.fresh(s: Ad.Sts, +k: Nat, +c: Ad.Cls) -> {Admission.adl_keep(s, k, c, Nil{}) == Ad.lv.fresh(s, k, c) : List<&2, Ad.Lv>}:
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

def al.keep_app(s: Ad.Sts, +k: Nat, +c: Ad.Cls, a: List<&2, Ad.Lv>, b: List<&2, Ad.Lv>) -> {List.append(&2, Ad.Lv, Admission.adl_keep(s, k, c, a), b) == Admission.adl_keep(s, k, c, List.append(&2, Ad.Lv, a, b)) : List<&2, Ad.Lv>}:
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

# a ticket appended to the model's tickets is the live ticket appended
def al.app(a: List<&2, Ad.Tk>, +c: Ad.Cls, +s: Ad.Sts, +j: Nat) -> {Admission.adl_lives(List.append(&2, Ad.Tk, a, [Ad.Tk{c, s}]), j) == List.append(&2, Ad.Lv, Admission.adl_lives(a, j), Ad.lv.fresh(s, Nat.add(List.length(&2, Ad.Tk, a), j), c)) : List<&2, Ad.Lv>}:
  match a:
    case Nil{}:
      al.fresh(s, j, c)
    case Ad.Tk{+c2, +s2} <> +r:
      +x = {Ad.Tk{c, s} : Ad.Tk}
      +n = {List.length(&2, Ad.Tk, r) : Nat}
      %Equal.sym(List<&2, Ad.Lv>, Admission.adl_lives(List.append(&2, Ad.Tk, r, [x]), 1n+j), List.append(&2, Ad.Lv, Admission.adl_lives(r, 1n+j), Ad.lv.fresh(s, Nat.add(n, 1n+j), c)), al.app(r, c, s, 1n+j)) : {Admission.adl_keep(s2, j, c2, _) == List.append(&2, Ad.Lv, Admission.adl_keep(s2, j, c2, Admission.adl_lives(r, 1n+j)), Ad.lv.fresh(s, 1n+Nat.add(n, j), c)) : List<&2, Ad.Lv>}
      %Equal.sym(Nat, Nat.add(n, 1n+j), 1n+Nat.add(n, j), al.add_succ(n, j)) : {Admission.adl_keep(s2, j, c2, List.append(&2, Ad.Lv, Admission.adl_lives(r, 1n+j), Ad.lv.fresh(s, _, c))) == List.append(&2, Ad.Lv, Admission.adl_keep(s2, j, c2, Admission.adl_lives(r, 1n+j)), Ad.lv.fresh(s, 1n+Nat.add(n, j), c)) : List<&2, Ad.Lv>}
      Equal.sym(List<&2, Ad.Lv>, List.append(&2, Ad.Lv, Admission.adl_keep(s2, j, c2, Admission.adl_lives(r, 1n+j)), Ad.lv.fresh(s, 1n+Nat.add(n, j), c)), Admission.adl_keep(s2, j, c2, List.append(&2, Ad.Lv, Admission.adl_lives(r, 1n+j), Ad.lv.fresh(s, 1n+Nat.add(n, j), c))), al.keep_app(s2, j, c2, Admission.adl_lives(r, 1n+j), Ad.lv.fresh(s, 1n+Nat.add(n, j), c)))

def al.admit_ia(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>) -> {Ad.lv.admit.ia(l, q, Admission.adl_lives(ts, 0n), List.length(&2, Ad.Tk, ts)) == Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n) : List<&2, Ad.Lv>}:
  +st = {Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts))) : Ad.Sts}
  %al.cnt_s(Ad.Waiting{}, Ad.Ia{}, ts, 0n) : {List.append(&2, Ad.Lv, Ad.lv.preempt(Admission.adl_lives(ts, 0n)), Ad.lv.fresh(Ad.admit.ia.st(Bool.and(Ad.isz(_), Ad.room(l, Ad.lv.cnt(Ad.Holding{}, Ad.Ia{}, Admission.adl_lives(ts, 0n)))), Ad.le(q, _)), List.length(&2, Ad.Tk, ts), Ad.Ia{})) == Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n) : List<&2, Ad.Lv>}
  %al.cnt_s(Ad.Holding{}, Ad.Ia{}, ts, 0n) : {List.append(&2, Ad.Lv, Ad.lv.preempt(Admission.adl_lives(ts, 0n)), Ad.lv.fresh(Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, _)), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts))), List.length(&2, Ad.Tk, ts), Ad.Ia{})) == Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n) : List<&2, Ad.Lv>}
  %Equal.sym(List<&2, Ad.Lv>, Ad.lv.preempt(Admission.adl_lives(ts, 0n)), Admission.adl_lives(Ad.preempt(ts), 0n), al.preempt(ts, 0n)) : {List.append(&2, Ad.Lv, _, Ad.lv.fresh(st, List.length(&2, Ad.Tk, ts), Ad.Ia{})) == Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n) : List<&2, Ad.Lv>}
  %Equal.sym(List<&2, Ad.Lv>, Admission.adl_lives(List.append(&2, Ad.Tk, Ad.preempt(ts), [Ad.Tk{Ad.Ia{}, st}]), 0n), List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, Nat.add(List.length(&2, Ad.Tk, Ad.preempt(ts)), 0n), Ad.Ia{})), al.app(Ad.preempt(ts), Ad.Ia{}, st, 0n)) : {List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, List.length(&2, Ad.Tk, ts), Ad.Ia{})) == _ : List<&2, Ad.Lv>}
  %Equal.sym(Nat, Nat.add(List.length(&2, Ad.Tk, Ad.preempt(ts)), 0n), List.length(&2, Ad.Tk, Ad.preempt(ts)), al.add_zero(List.length(&2, Ad.Tk, Ad.preempt(ts)))) : {List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, List.length(&2, Ad.Tk, ts), Ad.Ia{})) == List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, _, Ad.Ia{})) : List<&2, Ad.Lv>}
  %al.len_pre(ts) : {List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, _, Ad.Ia{})) == List.append(&2, Ad.Lv, Admission.adl_lives(Ad.preempt(ts), 0n), Ad.lv.fresh(st, List.length(&2, Ad.Tk, Ad.preempt(ts)), Ad.Ia{})) : List<&2, Ad.Lv>}
  {==}

def al.admit_bg(+l: Ad.Lim, +ts: List<&2, Ad.Tk>) -> {Ad.lv.admit.bg(l, Admission.adl_lives(ts, 0n), List.length(&2, Ad.Tk, ts)) == Admission.adl_lives(Ad.admit.bg(l, ts), 0n) : List<&2, Ad.Lv>}:
  +st = {Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts)))))) : Ad.Sts}
  %al.cnt_s(Ad.Holding{}, Ad.Ia{}, ts, 0n) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(Ad.admit.bg.st(Bool.and(Ad.isz(_), Bool.and(Ad.isz(Ad.lv.cnt(Ad.Waiting{}, Ad.Ia{}, Admission.adl_lives(ts, 0n))), Bool.and(Ad.isz(Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, 0n))), Ad.room(l, Ad.lv.held(Admission.adl_lives(ts, 0n))))))), List.length(&2, Ad.Tk, ts), Ad.Bg{})) == Admission.adl_lives(Ad.admit.bg(l, ts), 0n) : List<&2, Ad.Lv>}
  %al.cnt_s(Ad.Waiting{}, Ad.Ia{}, ts, 0n) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(_), Bool.and(Ad.isz(Ad.lv.cnt(Ad.Waiting{}, Ad.Bg{}, Admission.adl_lives(ts, 0n))), Ad.room(l, Ad.lv.held(Admission.adl_lives(ts, 0n))))))), List.length(&2, Ad.Tk, ts), Ad.Bg{})) == Admission.adl_lives(Ad.admit.bg(l, ts), 0n) : List<&2, Ad.Lv>}
  %al.cnt_s(Ad.Waiting{}, Ad.Bg{}, ts, 0n) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(_), Ad.room(l, Ad.lv.held(Admission.adl_lives(ts, 0n))))))), List.length(&2, Ad.Tk, ts), Ad.Bg{})) == Admission.adl_lives(Ad.admit.bg(l, ts), 0n) : List<&2, Ad.Lv>}
  %Equal.sym(Nat, Ad.lv.held(Admission.adl_lives(ts, 0n)), Ad.held(ts), al.held(ts, 0n)) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, _))))), List.length(&2, Ad.Tk, ts), Ad.Bg{})) == Admission.adl_lives(Ad.admit.bg(l, ts), 0n) : List<&2, Ad.Lv>}
  %Equal.sym(List<&2, Ad.Lv>, Admission.adl_lives(List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, st}]), 0n), List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(st, Nat.add(List.length(&2, Ad.Tk, ts), 0n), Ad.Bg{})), al.app(ts, Ad.Bg{}, st, 0n)) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(st, List.length(&2, Ad.Tk, ts), Ad.Bg{})) == _ : List<&2, Ad.Lv>}
  %Equal.sym(Nat, Nat.add(List.length(&2, Ad.Tk, ts), 0n), List.length(&2, Ad.Tk, ts), al.add_zero(List.length(&2, Ad.Tk, ts))) : {List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(st, List.length(&2, Ad.Tk, ts), Ad.Bg{})) == List.append(&2, Ad.Lv, Admission.adl_lives(ts, 0n), Ad.lv.fresh(st, _, Ad.Bg{})) : List<&2, Ad.Lv>}
  {==}

# Finding, setting and dropping a ticket by its number
# ----------------------------------------------------

# the status of a model ticket as the live controller finds it
def al.st(m: Maybe<&2, Ad.Tk>) -> Maybe<&2, Ad.Sts>:
  match m:
    case None{}:
      None{}
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      Some{Ad.Queued{}}
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      Some{Ad.Granted{}}
    case Some{Ad.Tk{c, Ad.Held{}}}:
      Some{Ad.Held{}}
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      Some{Ad.Preempted{}}
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      None{}

# a ticket numbered below the first is not found
def al.find_none(ts: List<&2, Ad.Tk>, +d: Nat, +j: Nat) -> {Ad.lv.find(Admission.adl_lives(ts, 1n+Nat.add(d, j)), j) == None{} : Maybe<&2, Ad.Sts>}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{c, s} <> +r:
      match s:
        case Ad.Queued{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.find.at(_, Ad.Queued{}, Ad.lv.find(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == None{} : Maybe<&2, Ad.Sts>}
          al.find_none(r, 1n+d, j)
        case Ad.Granted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.find.at(_, Ad.Granted{}, Ad.lv.find(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == None{} : Maybe<&2, Ad.Sts>}
          al.find_none(r, 1n+d, j)
        case Ad.Held{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.find.at(_, Ad.Held{}, Ad.lv.find(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == None{} : Maybe<&2, Ad.Sts>}
          al.find_none(r, 1n+d, j)
        case Ad.Preempted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.find.at(_, Ad.Preempted{}, Ad.lv.find(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == None{} : Maybe<&2, Ad.Sts>}
          al.find_none(r, 1n+d, j)
        case Ad.Ended{}:
          al.find_none(r, 1n+d, j)

def al.set_none(ts: List<&2, Ad.Tk>, +d: Nat, +j: Nat) -> {Ad.lv.set(Admission.adl_lives(ts, 1n+Nat.add(d, j)), j, Ad.Held{}) == Admission.adl_lives(ts, 1n+Nat.add(d, j)) : List<&2, Ad.Lv>}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{+c, s} <> +r:
      match s:
        case Ad.Queued{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.set.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}} <> x, Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.set_none(r, 1n+d, j))
        case Ad.Granted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.set.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}} <> x, Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.set_none(r, 1n+d, j))
        case Ad.Held{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.set.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.set_none(r, 1n+d, j))
        case Ad.Preempted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.set.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}} <> x, Ad.lv.set(Admission.adl_lives(r, 2n+Nat.add(d, j)), j, Ad.Held{}), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.set_none(r, 1n+d, j))
        case Ad.Ended{}:
          al.set_none(r, 1n+d, j)

def al.drop_none(ts: List<&2, Ad.Tk>, +d: Nat, +j: Nat) -> {Ad.lv.drop(Admission.adl_lives(ts, 1n+Nat.add(d, j)), j) == Admission.adl_lives(ts, 1n+Nat.add(d, j)) : List<&2, Ad.Lv>}:
  match ts:
    case Nil{}:
      {==}
    case Ad.Tk{+c, s} <> +r:
      match s:
        case Ad.Queued{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.drop.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}}, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Queued{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.drop_none(r, 1n+d, j))
        case Ad.Granted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.drop.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}}, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Granted{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.drop_none(r, 1n+d, j))
        case Ad.Held{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.drop.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}}, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Held{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.drop_none(r, 1n+d, j))
        case Ad.Preempted{}:
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(d, j), j), False{}, al.ne_add2(d, j)) : {Ad.lv.drop.at(_, Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}}, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j)) == Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}} <> Admission.adl_lives(r, 2n+Nat.add(d, j)) : List<&2, Ad.Lv>}
          Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{1n+Nat.add(d, j), c, Ad.Preempted{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 2n+Nat.add(d, j)), j), Admission.adl_lives(r, 2n+Nat.add(d, j)), al.drop_none(r, 1n+d, j))
        case Ad.Ended{}:
          al.drop_none(r, 1n+d, j)

def al.find0(s: Ad.Sts, c: Ad.Cls, +r: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.find(Admission.adl_lives(Ad.Tk{c, s} <> r, j), j) == al.st(Some{Ad.Tk{c, s}}) : Maybe<&2, Ad.Sts>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.find.at(_, Ad.Queued{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), j)) == Some{Ad.Queued{}} : Maybe<&2, Ad.Sts>}
      {==}
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.find.at(_, Ad.Granted{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), j)) == Some{Ad.Granted{}} : Maybe<&2, Ad.Sts>}
      {==}
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.find.at(_, Ad.Held{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), j)) == Some{Ad.Held{}} : Maybe<&2, Ad.Sts>}
      {==}
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.find.at(_, Ad.Preempted{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), j)) == Some{Ad.Preempted{}} : Maybe<&2, Ad.Sts>}
      {==}
    case Ad.Ended{}:
      al.find_none(r, 0n, j)

def al.find1(s: Ad.Sts, c: Ad.Cls, +r: List<&2, Ad.Tk>, +p: Nat, +j: Nat, ih: {Ad.lv.find(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)) == al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}) -> {Ad.lv.find(Admission.adl_lives(Ad.Tk{c, s} <> r, j), 1n+Nat.add(p, j)) == al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.find.at(_, Ad.Queued{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      %al.add_succ(p, j) : {Ad.lv.find(Admission.adl_lives(r, 1n+j), _) == al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      ih
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.find.at(_, Ad.Granted{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      %al.add_succ(p, j) : {Ad.lv.find(Admission.adl_lives(r, 1n+j), _) == al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      ih
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.find.at(_, Ad.Held{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      %al.add_succ(p, j) : {Ad.lv.find(Admission.adl_lives(r, 1n+j), _) == al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      ih
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.find.at(_, Ad.Preempted{}, Ad.lv.find(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      %al.add_succ(p, j) : {Ad.lv.find(Admission.adl_lives(r, 1n+j), _) == al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      ih
    case Ad.Ended{}:
      %al.add_succ(p, j) : {Ad.lv.find(Admission.adl_lives(r, 1n+j), _) == al.st(List.get(&2, Ad.Tk, r, p)) : Maybe<&2, Ad.Sts>}
      ih

# the live controller finds ticket i of the model (numbered from j)
def al.find(ts: List<&2, Ad.Tk>, i: Nat, +j: Nat) -> {Ad.lv.find(Admission.adl_lives(ts, j), Nat.add(i, j)) == al.st(List.get(&2, Ad.Tk, ts, i)) : Maybe<&2, Ad.Sts>}:
  match ts i:
    case Nil{} _:
      {==}
    case Ad.Tk{c, s} <> +r 0n:
      al.find0(s, c, r, j)
    case Ad.Tk{c, s} <> +r 1n++p:
      al.find1(s, c, r, p, j, al.find(r, p, 1n+j))

def al.set0(s: Ad.Sts, +c: Ad.Cls, +r: List<&2, Ad.Tk>, +j: Nat, ne: {Ad.ended(Some{Ad.Tk{c, s}}) == False{} : Bool}) -> {Ad.lv.set(Admission.adl_lives(Ad.Tk{c, s} <> r, j), j, Ad.Held{}) == Admission.adl_lives(Ad.put(Ad.Tk{c, s} <> r, 0n, Ad.Held{}), j) : List<&2, Ad.Lv>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Queued{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}), Admission.adl_lives(r, 1n+j), al.set_none(r, 0n, j))
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Granted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}), Admission.adl_lives(r, 1n+j), al.set_none(r, 0n, j))
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Held{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}), Admission.adl_lives(r, 1n+j), al.set_none(r, 0n, j))
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Preempted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}), Admission.adl_lives(r, 1n+j), al.set_none(r, 0n, j))
    case Ad.Ended{}:
      al.absurd({Ad.lv.set(Admission.adl_lives(r, 1n+j), j, Ad.Held{}) == Admission.adl_lives(Ad.Tk{c, Ad.Held{}} <> r, j) : List<&2, Ad.Lv>}, ne)

def al.set1(s: Ad.Sts, +c: Ad.Cls, +r: List<&2, Ad.Tk>, +p: Nat, +j: Nat, ih: {Ad.lv.set(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j), Ad.Held{}) == Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}) -> {Ad.lv.set(Admission.adl_lives(Ad.Tk{c, s} <> r, j), 1n+Nat.add(p, j), Ad.Held{}) == Admission.adl_lives(Ad.put(Ad.Tk{c, s} <> r, 1n+p, Ad.Held{}), j) : List<&2, Ad.Lv>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Queued{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j), Ad.Held{}) == Ad.Lv{j, c, Ad.Queued{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      %al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Queued{}} <> Ad.lv.set(Admission.adl_lives(r, 1n+j), _, Ad.Held{}) == Ad.Lv{j, c, Ad.Queued{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Queued{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j), Ad.Held{}), Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j), ih)
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Granted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j), Ad.Held{}) == Ad.Lv{j, c, Ad.Granted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      %al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Granted{}} <> Ad.lv.set(Admission.adl_lives(r, 1n+j), _, Ad.Held{}) == Ad.Lv{j, c, Ad.Granted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Granted{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j), Ad.Held{}), Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j), ih)
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Held{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j), Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      %al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Held{}} <> Ad.lv.set(Admission.adl_lives(r, 1n+j), _, Ad.Held{}) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j), Ad.Held{}), Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j), ih)
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.set.at(_, Ad.Lv{j, c, Ad.Preempted{}}, Ad.Held{}) <> Ad.lv.set(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j), Ad.Held{}) == Ad.Lv{j, c, Ad.Preempted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      %al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Preempted{}} <> Ad.lv.set(Admission.adl_lives(r, 1n+j), _, Ad.Held{}) == Ad.Lv{j, c, Ad.Preempted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Preempted{}} <> x, Ad.lv.set(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j), Ad.Held{}), Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j), ih)
    case Ad.Ended{}:
      %al.add_succ(p, j) : {Ad.lv.set(Admission.adl_lives(r, 1n+j), _, Ad.Held{}) == Admission.adl_lives(Ad.put(r, p, Ad.Held{}), 1n+j) : List<&2, Ad.Lv>}
      ih

def al.set(ts: List<&2, Ad.Tk>, i: Nat, +j: Nat, ne: {Ad.ended(List.get(&2, Ad.Tk, ts, i)) == False{} : Bool}) -> {Ad.lv.set(Admission.adl_lives(ts, j), Nat.add(i, j), Ad.Held{}) == Admission.adl_lives(Ad.put(ts, i, Ad.Held{}), j) : List<&2, Ad.Lv>}:
  match ts i:
    case Nil{} _:
      {==}
    case Ad.Tk{+c, +s} <> +r 0n:
      al.set0(s, c, r, j, ne)
    case Ad.Tk{+c, +s} <> +r 1n++p:
      al.set1(s, c, r, p, j, al.set(r, p, 1n+j, ne))

def al.drop0(s: Ad.Sts, +c: Ad.Cls, +r: List<&2, Ad.Tk>, +j: Nat) -> {Ad.lv.drop(Admission.adl_lives(Ad.Tk{c, s} <> r, j), j) == Admission.adl_lives(Ad.put(Ad.Tk{c, s} <> r, 0n, Ad.Ended{}), j) : List<&2, Ad.Lv>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Queued{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), j)) == Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      al.drop_none(r, 0n, j)
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Granted{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), j)) == Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      al.drop_none(r, 0n, j)
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Held{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), j)) == Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      al.drop_none(r, 0n, j)
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, al.eq_refl(j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Preempted{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), j)) == Admission.adl_lives(r, 1n+j) : List<&2, Ad.Lv>}
      al.drop_none(r, 0n, j)
    case Ad.Ended{}:
      al.drop_none(r, 0n, j)

def al.drop1(s: Ad.Sts, +c: Ad.Cls, +r: List<&2, Ad.Tk>, +p: Nat, +j: Nat, ih: {Ad.lv.drop(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)) == Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}) -> {Ad.lv.drop(Admission.adl_lives(Ad.Tk{c, s} <> r, j), 1n+Nat.add(p, j)) == Admission.adl_lives(Ad.put(Ad.Tk{c, s} <> r, 1n+p, Ad.Ended{}), j) : List<&2, Ad.Lv>}:
  match s:
    case Ad.Queued{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Queued{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == Ad.Lv{j, c, Ad.Queued{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      %al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Queued{}} <> Ad.lv.drop(Admission.adl_lives(r, 1n+j), _) == Ad.Lv{j, c, Ad.Queued{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Queued{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)), Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j), ih)
    case Ad.Granted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Granted{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == Ad.Lv{j, c, Ad.Granted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      %al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Granted{}} <> Ad.lv.drop(Admission.adl_lives(r, 1n+j), _) == Ad.Lv{j, c, Ad.Granted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Granted{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)), Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j), ih)
    case Ad.Held{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Held{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      %al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Held{}} <> Ad.lv.drop(Admission.adl_lives(r, 1n+j), _) == Ad.Lv{j, c, Ad.Held{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Held{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)), Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j), ih)
    case Ad.Preempted{}:
      %Equal.sym(Bool, Nat.is_eq(j, 1n+Nat.add(p, j)), False{}, al.ne_add(p, j)) : {Ad.lv.drop.at(_, Ad.Lv{j, c, Ad.Preempted{}}, Ad.lv.drop(Admission.adl_lives(r, 1n+j), 1n+Nat.add(p, j))) == Ad.Lv{j, c, Ad.Preempted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      %al.add_succ(p, j) : {Ad.Lv{j, c, Ad.Preempted{}} <> Ad.lv.drop(Admission.adl_lives(r, 1n+j), _) == Ad.Lv{j, c, Ad.Preempted{}} <> Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      Equal.cong(List<&2, Ad.Lv>, List<&2, Ad.Lv>, x => Ad.Lv{j, c, Ad.Preempted{}} <> x, Ad.lv.drop(Admission.adl_lives(r, 1n+j), Nat.add(p, 1n+j)), Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j), ih)
    case Ad.Ended{}:
      %al.add_succ(p, j) : {Ad.lv.drop(Admission.adl_lives(r, 1n+j), _) == Admission.adl_lives(Ad.put(r, p, Ad.Ended{}), 1n+j) : List<&2, Ad.Lv>}
      ih

def al.drop(ts: List<&2, Ad.Tk>, i: Nat, +j: Nat) -> {Ad.lv.drop(Admission.adl_lives(ts, j), Nat.add(i, j)) == Admission.adl_lives(Ad.put(ts, i, Ad.Ended{}), j) : List<&2, Ad.Lv>}:
  match ts i:
    case Nil{} _:
      {==}
    case Ad.Tk{+c, +s} <> +r 0n:
      al.drop0(s, c, r, j)
    case Ad.Tk{+c, +s} <> +r 1n++p:
      al.drop1(s, c, r, p, j, al.drop(r, p, 1n+j))

# Lengths of an admit
def al.len_admit_ia(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>) -> {List.length(&2, Ad.Tk, Ad.admit.ia(l, q, ts)) == 1n+List.length(&2, Ad.Tk, ts) : Nat}:
  +x = {Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)))} : Ad.Tk}
  Equal.trans(Nat, List.length(&2, Ad.Tk, List.append(&2, Ad.Tk, Ad.preempt(ts), [x])), 1n+List.length(&2, Ad.Tk, Ad.preempt(ts)), 1n+List.length(&2, Ad.Tk, ts), al.len_app1(Ad.preempt(ts), x), Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Ad.Tk, Ad.preempt(ts)), List.length(&2, Ad.Tk, ts), al.len_pre(ts)))

# ---- the step ----

def al.col(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, eq: {List.get(&2, Ad.Tk, ts, k) == m : Maybe<&2, Ad.Tk>}) -> {Ad.Live{l, q, Ad.lv.collect(al.st(m), Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.collect.at(m, l, q, ts, k)) : Ad.Live}:
  match m:
    case None{}:
      {==}
    case Some{Ad.Tk{c, Ad.Queued{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      %al.add_zero(k) : {Ad.Live{l, q, Ad.lv.set(Admission.adl_lives(ts, 0n), _, Ad.Held{}), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.put(ts, k, Ad.Held{})}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.set(Admission.adl_lives(ts, 0n), Nat.add(k, 0n), Ad.Held{}), Admission.adl_lives(Ad.put(ts, k, Ad.Held{}), 0n), al.set(ts, k, 0n, Equal.trans(Bool, Ad.ended(List.get(&2, Ad.Tk, ts, k)), Ad.ended(Some{Ad.Tk{c, Ad.Granted{}}}), False{}, Equal.cong(Maybe<&2, Ad.Tk>, Bool, x => Ad.ended(x), List.get(&2, Ad.Tk, ts, k), Some{Ad.Tk{c, Ad.Granted{}}}, eq), {==}))) : {Ad.Live{l, q, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.put(ts, k, Ad.Held{})}) : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Held{})), List.length(&2, Ad.Tk, ts), al.len_put(ts, k, Ad.Held{})) : {Ad.Live{l, q, Admission.adl_lives(Ad.put(ts, k, Ad.Held{}), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.put(ts, k, Ad.Held{}), 0n), _} : Ad.Live}
      {==}
    case Some{Ad.Tk{c, Ad.Held{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Ended{}}}:
{==}

def al.rel(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, eq: {List.get(&2, Ad.Tk, ts, k) == m : Maybe<&2, Ad.Tk>}) -> {Ad.Live{l, q, Ad.lv.release(al.st(m), l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.release.at(m, l, q, ts, k)) : Ad.Live}:
  match m:
    case None{}:
      {==}
    case Some{Ad.Tk{c, Ad.Queued{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Granted{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Held{}}}:
      %al.add_zero(k) : {Ad.Live{l, q, Ad.lv.grant(l, Ad.lv.drop(Admission.adl_lives(ts, 0n), _)), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.drop(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), al.drop(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.grant(l, _), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.grant(l, Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n)), Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), al.grant(l, Ad.put(ts, k, Ad.Ended{}), 0n)) : {Ad.Live{l, q, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))), List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), al.len_grant(l, Ad.put(ts, k, Ad.Ended{}))) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), List.length(&2, Ad.Tk, ts), al.len_put(ts, k, Ad.Ended{})) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      {==}
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      %al.add_zero(k) : {Ad.Live{l, q, Ad.lv.drop(Admission.adl_lives(ts, 0n), _), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.put(ts, k, Ad.Ended{})}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.drop(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), al.drop(ts, k, 0n)) : {Ad.Live{l, q, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.put(ts, k, Ad.Ended{})}) : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), List.length(&2, Ad.Tk, ts), al.len_put(ts, k, Ad.Ended{})) : {Ad.Live{l, q, Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), _} : Ad.Live}
      {==}
    case Some{Ad.Tk{c, Ad.Ended{}}}:
{==}

def al.lea(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, eq: {List.get(&2, Ad.Tk, ts, k) == m : Maybe<&2, Ad.Tk>}) -> {Ad.Live{l, q, Ad.lv.leave(al.st(m), l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.leave.at(m, l, q, ts, k)) : Ad.Live}:
  match m:
    case None{}:
      {==}
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      %al.add_zero(k) : {Ad.Live{l, q, Ad.lv.grant(l, Ad.lv.drop(Admission.adl_lives(ts, 0n), _)), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.drop(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), al.drop(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.grant(l, _), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.grant(l, Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n)), Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), al.grant(l, Ad.put(ts, k, Ad.Ended{}), 0n)) : {Ad.Live{l, q, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))), List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), al.len_grant(l, Ad.put(ts, k, Ad.Ended{}))) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), List.length(&2, Ad.Tk, ts), al.len_put(ts, k, Ad.Ended{})) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      {==}
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      %al.add_zero(k) : {Ad.Live{l, q, Ad.lv.grant(l, Ad.lv.drop(Admission.adl_lives(ts, 0n), _)), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.drop(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n), al.drop(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.grant(l, _), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(List<&2, Ad.Lv>, Ad.lv.grant(l, Admission.adl_lives(Ad.put(ts, k, Ad.Ended{}), 0n)), Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), al.grant(l, Ad.put(ts, k, Ad.Ended{}), 0n)) : {Ad.Live{l, q, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))}) : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))), List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), al.len_grant(l, Ad.put(ts, k, Ad.Ended{}))) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.put(ts, k, Ad.Ended{})), List.length(&2, Ad.Tk, ts), al.len_put(ts, k, Ad.Ended{})) : {Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.grant(l, Ad.put(ts, k, Ad.Ended{})), 0n), _} : Ad.Live}
      {==}
    case Some{Ad.Tk{c, Ad.Held{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
{==}
    case Some{Ad.Tk{c, Ad.Ended{}}}:
{==}

def al.step(s: Ad.St, o: Ad.Op) -> {Ad.Live.step(Admission.adl_live(s), o) == Admission.adl_live(Ad.step(s, o)) : Ad.Live}:
  match s:
    case Ad.St{+l, +q, +ts}:
      match o:
        case Ad.Admit{c}:
          match c:
            case Ad.Ia{}:
              %Equal.sym(List<&2, Ad.Lv>, Ad.lv.admit.ia(l, q, Admission.adl_lives(ts, 0n), List.length(&2, Ad.Tk, ts)), Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n), al.admit_ia(l, q, ts)) : {Ad.Live{l, q, _, 1n+List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Ia{}})) : Ad.Live}
              %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.admit.ia(l, q, ts)), 1n+List.length(&2, Ad.Tk, ts), al.len_admit_ia(l, q, ts)) : {Ad.Live{l, q, Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n), 1n+List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.admit.ia(l, q, ts), 0n), _} : Ad.Live}
              {==}
            case Ad.Bg{}:
              %Equal.sym(List<&2, Ad.Lv>, Ad.lv.admit.bg(l, Admission.adl_lives(ts, 0n), List.length(&2, Ad.Tk, ts)), Admission.adl_lives(Ad.admit.bg(l, ts), 0n), al.admit_bg(l, ts)) : {Ad.Live{l, q, _, 1n+List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Bg{}})) : Ad.Live}
              %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.admit.bg(l, ts)), 1n+List.length(&2, Ad.Tk, ts), al.len_app1(ts, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts))))))})) : {Ad.Live{l, q, Admission.adl_lives(Ad.admit.bg(l, ts), 0n), 1n+List.length(&2, Ad.Tk, ts)} == Ad.Live{l, q, Admission.adl_lives(Ad.admit.bg(l, ts), 0n), _} : Ad.Live}
              {==}
        case Ad.Collect{+k}:
          %al.add_zero(k) : {Ad.Live{l, q, Ad.lv.collect(Ad.lv.find(Admission.adl_lives(ts, 0n), _), Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Collect{k})) : Ad.Live}
          %Equal.sym(Maybe<&2, Ad.Sts>, Ad.lv.find(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), al.st(List.get(&2, Ad.Tk, ts, k)), al.find(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.collect(_, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Collect{k})) : Ad.Live}
          al.col(List.get(&2, Ad.Tk, ts, k), l, q, ts, k, {==})
        case Ad.Release{+k}:
          %al.add_zero(k) : {Ad.Live{l, q, Ad.lv.release(Ad.lv.find(Admission.adl_lives(ts, 0n), _), l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Release{k})) : Ad.Live}
          %Equal.sym(Maybe<&2, Ad.Sts>, Ad.lv.find(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), al.st(List.get(&2, Ad.Tk, ts, k)), al.find(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.release(_, l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Release{k})) : Ad.Live}
          al.rel(List.get(&2, Ad.Tk, ts, k), l, q, ts, k, {==})
        case Ad.Leave{+k}:
          %al.add_zero(k) : {Ad.Live{l, q, Ad.lv.leave(Ad.lv.find(Admission.adl_lives(ts, 0n), _), l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Leave{k})) : Ad.Live}
          %Equal.sym(Maybe<&2, Ad.Sts>, Ad.lv.find(Admission.adl_lives(ts, 0n), Nat.add(k, 0n)), al.st(List.get(&2, Ad.Tk, ts, k)), al.find(ts, k, 0n)) : {Ad.Live{l, q, Ad.lv.leave(_, l, Admission.adl_lives(ts, 0n), k), List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Leave{k})) : Ad.Live}
          al.lea(List.get(&2, Ad.Tk, ts, k), l, q, ts, k, {==})
        case Ad.Limit{+l2, q2}:
          %Equal.sym(List<&2, Ad.Lv>, Ad.lv.grant(l2, Admission.adl_lives(ts, 0n)), Admission.adl_lives(Ad.grant(l2, ts), 0n), al.grant(l2, ts, 0n)) : {Ad.Live{l2, q2, _, List.length(&2, Ad.Tk, ts)} == Admission.adl_live(Ad.step(Ad.St{l, q, ts}, Ad.Limit{l2, q2})) : Ad.Live}
          %Equal.sym(Nat, List.length(&2, Ad.Tk, Ad.grant(l2, ts)), List.length(&2, Ad.Tk, ts), al.len_grant(l2, ts)) : {Ad.Live{l2, q2, Admission.adl_lives(Ad.grant(l2, ts), 0n), List.length(&2, Ad.Tk, ts)} == Ad.Live{l2, q2, Admission.adl_lives(Ad.grant(l2, ts), 0n), _} : Ad.Live}
          {==}

# ---- admission_wire ----

# Place after PROOF.bend section wire: the proofs use its Laws.wire_*
# fills and wr_and_l / wr_and_r.

# a Nat that fits reads back (Laws.wire_nat_round_trip, turned around)
def paw.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def Admission.adw_lim_round_trip(l, rest, h):
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{+p}:
      %paw.nat(p, rest, h) : {FAd.get_lim.cap(_) == Wr.Got{Ad.Cap{p}, rest} : Wr.Dec<Ad.Lim>}
      {==}

# a cls reads back (turned around for rewriting)
def paw.cls(+c: Ad.Cls, +rest: String) -> {Wr.Got{c, rest} == FAd.get_cls(FAd.put_cls(c, rest)) : Wr.Dec<Ad.Cls>}:
  Equal.sym(Wr.Dec<Ad.Cls>, FAd.get_cls(FAd.put_cls(c, rest)), Wr.Got{c, rest}, Admission.adw_cls_round_trip(c, rest))

# a lim reads back (turned around for rewriting)
def paw.lim(+l: Ad.Lim, +rest: String, h: {Admission.adw_lim_fits(l) == True{} : Bool}) -> {Wr.Got{l, rest} == FAd.get_lim(FAd.put_lim(l, rest)) : Wr.Dec<Ad.Lim>}:
  Equal.sym(Wr.Dec<Ad.Lim>, FAd.get_lim(FAd.put_lim(l, rest)), Wr.Got{l, rest}, Admission.adw_lim_round_trip(l, rest, h))

def Admission.adw_op_round_trip(o, rest, h):
  match o:
    case Ad.Admit{+c}:
      %paw.cls(c, rest) : {FAd.get_op.admit(_) == Wr.Got{Ad.Admit{c}, rest} : Wr.Dec<Ad.Op>}
      {==}
    case Ad.Collect{+k}:
      %paw.nat(k, rest, h) : {FAd.get_op.k(_, 0n) == Wr.Got{Ad.Collect{k}, rest} : Wr.Dec<Ad.Op>}
      {==}
    case Ad.Release{+k}:
      %paw.nat(k, rest, h) : {FAd.get_op.k(_, 1n) == Wr.Got{Ad.Release{k}, rest} : Wr.Dec<Ad.Op>}
      {==}
    case Ad.Leave{+k}:
      %paw.nat(k, rest, h) : {FAd.get_op.k(_, 2n) == Wr.Got{Ad.Leave{k}, rest} : Wr.Dec<Ad.Op>}
      {==}
    case Ad.Limit{+l, +q}:
      +r = rest
      +hh = h
      %paw.lim(l, Wr.put_nat(q, r), L.wr_and_l(Admission.adw_lim_fits(l), LawsBase.wire_fits(q), hh)) : {FAd.get_op.limit(_) == Wr.Got{Ad.Limit{l, q}, r} : Wr.Dec<Ad.Op>}
      %paw.nat(q, r, L.wr_and_r(Admission.adw_lim_fits(l), LawsBase.wire_fits(q), hh)) : {FAd.get_op.q(l, _) == Wr.Got{Ad.Limit{l, q}, r} : Wr.Dec<Ad.Op>}
      {==}

# a op reads back (turned around for rewriting)
def paw.op(+o: Ad.Op, +rest: String, h: {Admission.adw_op_fits(o) == True{} : Bool}) -> {Wr.Got{o, rest} == FAd.get_op(FAd.put_op(o, rest)) : Wr.Dec<Ad.Op>}:
  Equal.sym(Wr.Dec<Ad.Op>, FAd.get_op(FAd.put_op(o, rest)), Wr.Got{o, rest}, Admission.adw_op_round_trip(o, rest, h))

def Admission.adw_open_round_trip(l, q, rest, h):
  +r = rest
  +hh = h
  %paw.lim(l, Wr.put_nat(q, r), L.wr_and_l(Admission.adw_lim_fits(l), LawsBase.wire_fits(q), hh)) : {FAd.get_open.go(_) == Wr.Got{(l, q), r} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}
  %paw.nat(q, r, L.wr_and_r(Admission.adw_lim_fits(l), LawsBase.wire_fits(q), hh)) : {FAd.get_open.q(l, _) == Wr.Got{(l, q), r} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}
  {==}

# an open request that fits reads back (turned around for rewriting)
def paw.open(+l: Ad.Lim, +q: Nat, +rest: String, h: {Bool.and(Admission.adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}) ->
  {Wr.Got{(l, q), rest} == FAd.get_open(FAd.put_lim(l, Wr.put_nat(q, rest))) : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}:
  Equal.sym(Wr.Dec<+Sigma<Ad.Lim, x => Nat>>, FAd.get_open(FAd.put_lim(l, Wr.put_nat(q, rest))), Wr.Got{(l, q), rest}, Admission.adw_open_round_trip(l, q, rest, h))

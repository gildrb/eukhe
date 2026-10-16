# proof_admission: the admission laws of LAWS.bend (rule H3 of
# docs/harness.md) over the model in admission.bend.

import Base
import ./admission.bend as A

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

def ad.bit_comm(a: Bool, b: Bool, -x: Nat) -> {A.bit(a, A.bit(b, x)) == A.bit(b, A.bit(a, x)) : Nat}:
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
def ad.cnt_app(+m: A.Mode, +c: A.Cls, t: List<&2, A.Tk>, +x: A.Tk) -> {A.cnt(m, c, List.append(&2, A.Tk, t, [x])) == A.bit(A.hit(m, c, x), A.cnt(m, c, t)) : Nat}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      %Equal.sym(Nat, A.cnt(m, c, List.append(&2, A.Tk, r, [x])), A.bit(A.hit(m, c, x), A.cnt(m, c, r)), ad.cnt_app(m, c, r, x)) : {A.bit(A.hit(m, c, h), _) == A.bit(A.hit(m, c, x), A.bit(A.hit(m, c, h), A.cnt(m, c, r))) : Nat}
      ad.bit_comm(A.hit(m, c, h), A.hit(m, c, x), A.cnt(m, c, r))

# what a count of mode m, class c sees of ticket mb
def ad.at(+m: A.Mode, +c: A.Cls, mb: Maybe<&2, A.Tk>) -> Bool:
  match mb:
    case None{}:
      False{}
    case Some{t}:
      A.hit(m, c, t)

# ticket mb with status x
def ad.set(mb: Maybe<&2, A.Tk>, x: A.Sts) -> Maybe<&2, A.Tk>:
  match mb:
    case None{}:
      None{}
    case Some{A.Tk{c, s}}:
      Some{A.Tk{c, x}}

# a ticket's new status counts in its place
def ad.cnt_put(+m: A.Mode, +c: A.Cls, t: List<&2, A.Tk>, +k: Nat, +x: A.Sts) -> {A.bit(ad.at(m, c, A.get(t, k)), A.cnt(m, c, A.put(t, k, x))) == A.bit(ad.at(m, c, ad.set(A.get(t, k), x)), A.cnt(m, c, t)) : Nat}:
  match t:
    case Nil{}:
      {==}
    case A.Tk{+c1, +s1} <> +r:
      match k:
        case 0n:
          ad.bit_comm(A.hit(m, c, A.Tk{c1, s1}), A.hit(m, c, A.Tk{c1, x}), A.cnt(m, c, r))
        case 1n+p:
          +ha = ad.at(m, c, A.get(r, p))
          +hs = ad.at(m, c, ad.set(A.get(r, p), x))
          +hh = A.hit(m, c, A.Tk{c1, s1})
          %ad.bit_comm(hh, ha, A.cnt(m, c, A.put(r, p, x))) : {_ == A.bit(hs, A.bit(hh, A.cnt(m, c, r))) : Nat}
          %Equal.sym(Nat, A.bit(ha, A.cnt(m, c, A.put(r, p, x))), A.bit(hs, A.cnt(m, c, r)), ad.cnt_put(m, c, r, p, x)) : {A.bit(hh, _) == A.bit(hs, A.bit(hh, A.cnt(m, c, r))) : Nat}
          ad.bit_comm(hh, hs, A.cnt(m, c, r))

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
def ad.hit_pre(+m: A.Mode, t: A.Tk) -> {A.hit(m, A.Ia{}, A.Tk.preempt(t)) == A.hit(m, A.Ia{}, t) : Bool}:
  match t:
    case A.Tk{A.Ia{}, s}:
      {==}
    case A.Tk{A.Bg{}, s}:
      match s:
        case A.Queued{}:
          {==}
        case A.Granted{}:
          ad.and_ff(A.Mode.of(m, A.Queued{}), A.Mode.of(m, A.Granted{}))
        case A.Held{}:
          ad.and_ff(A.Mode.of(m, A.Preempted{}), A.Mode.of(m, A.Held{}))
        case A.Preempted{}:
          {==}
        case A.Ended{}:
          {==}

def ad.pre_ia(+m: A.Mode, t: List<&2, A.Tk>) -> {A.cnt(m, A.Ia{}, A.preempt(t)) == A.cnt(m, A.Ia{}, t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      %Equal.sym(Bool, A.hit(m, A.Ia{}, A.Tk.preempt(h)), A.hit(m, A.Ia{}, h), ad.hit_pre(m, h)) : {A.bit(_, A.cnt(m, A.Ia{}, A.preempt(r))) == A.bit(A.hit(m, A.Ia{}, h), A.cnt(m, A.Ia{}, r)) : Nat}
      %Equal.sym(Nat, A.cnt(m, A.Ia{}, A.preempt(r)), A.cnt(m, A.Ia{}, r), ad.pre_ia(m, r)) : {A.bit(A.hit(m, A.Ia{}, h), _) == A.bit(A.hit(m, A.Ia{}, h), A.cnt(m, A.Ia{}, r)) : Nat}
      {==}

# it leaves no background slot held
def ad.hb_pre(t: A.Tk) -> {A.hit(A.Holding{}, A.Bg{}, A.Tk.preempt(t)) == False{} : Bool}:
  match t:
    case A.Tk{A.Ia{}, s}:
      ad.and_f(A.Mode.of(A.Holding{}, s))
    case A.Tk{A.Bg{}, s}:
      match s:
        case A.Queued{}:
          {==}
        case A.Granted{}:
          {==}
        case A.Held{}:
          {==}
        case A.Preempted{}:
          {==}
        case A.Ended{}:
          {==}

def ad.pre_hb(t: List<&2, A.Tk>) -> {A.cnt(A.Holding{}, A.Bg{}, A.preempt(t)) == 0n : Nat}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      %Equal.sym(Bool, A.hit(A.Holding{}, A.Bg{}, A.Tk.preempt(h)), False{}, ad.hb_pre(h)) : {A.bit(_, A.cnt(A.Holding{}, A.Bg{}, A.preempt(r))) == 0n : Nat}
      ad.pre_hb(r)

# A grant
# -------

# the grant passes a ticket that is not the oldest waiter of class c
def ad.mark_skip(+m: A.Mode, +d: A.Cls, +c: A.Cls, +h: A.Tk, +r: List<&2, A.Tk>, ih: {A.bit(A.hit(m, d, A.Tk{c, A.Queued{}}), A.cnt(m, d, A.mark(c, r))) == A.bit(A.hit(m, d, A.Tk{c, A.Granted{}}), A.cnt(m, d, r)) : Nat}) -> {A.bit(A.hit(m, d, A.Tk{c, A.Queued{}}), A.bit(A.hit(m, d, h), A.cnt(m, d, A.mark(c, r)))) == A.bit(A.hit(m, d, A.Tk{c, A.Granted{}}), A.bit(A.hit(m, d, h), A.cnt(m, d, r))) : Nat}:
  +hq = A.hit(m, d, A.Tk{c, A.Queued{}})
  +hg = A.hit(m, d, A.Tk{c, A.Granted{}})
  +hh = A.hit(m, d, h)
  %ad.bit_comm(hh, hq, A.cnt(m, d, A.mark(c, r))) : {_ == A.bit(hg, A.bit(hh, A.cnt(m, d, r))) : Nat}
  %Equal.sym(Nat, A.bit(hq, A.cnt(m, d, A.mark(c, r))), A.bit(hg, A.cnt(m, d, r)), ih) : {A.bit(hh, _) == A.bit(hg, A.bit(hh, A.cnt(m, d, r))) : Nat}
  ad.bit_comm(hh, hg, A.cnt(m, d, r))

# a grant to class c turns one waiter of c into a slot held
def ad.cnt_mark(+m: A.Mode, +d: A.Cls, t: List<&2, A.Tk>, +c: A.Cls, nz: {A.isz(A.cnt(A.Waiting{}, c, t)) == False{} : Bool}) -> {A.bit(A.hit(m, d, A.Tk{c, A.Queued{}}), A.cnt(m, d, A.mark(c, t))) == A.bit(A.hit(m, d, A.Tk{c, A.Granted{}}), A.cnt(m, d, t)) : Nat}:
  match t:
    case Nil{}:
      ad.absurd_t({A.bit(A.hit(m, d, A.Tk{c, A.Queued{}}), 0n) == A.bit(A.hit(m, d, A.Tk{c, A.Granted{}}), 0n) : Nat}, nz)
    case A.Tk{+hc, +hs} <> +r:
      match hc hs:
        case A.Ia{} A.Queued{}:
          match c:
            case A.Ia{}:
              ad.bit_comm(A.hit(m, d, A.Tk{A.Ia{}, A.Queued{}}), A.hit(m, d, A.Tk{A.Ia{}, A.Granted{}}), A.cnt(m, d, r))
            case A.Bg{}:
              ad.mark_skip(m, d, A.Bg{}, A.Tk{A.Ia{}, A.Queued{}}, r, ad.cnt_mark(m, d, r, A.Bg{}, nz))
        case A.Bg{} A.Queued{}:
          match c:
            case A.Ia{}:
              ad.mark_skip(m, d, A.Ia{}, A.Tk{A.Bg{}, A.Queued{}}, r, ad.cnt_mark(m, d, r, A.Ia{}, nz))
            case A.Bg{}:
              ad.bit_comm(A.hit(m, d, A.Tk{A.Bg{}, A.Queued{}}), A.hit(m, d, A.Tk{A.Bg{}, A.Granted{}}), A.cnt(m, d, r))
        case _ A.Granted{}:
          ad.mark_skip(m, d, c, A.Tk{hc, A.Granted{}}, r, ad.cnt_mark(m, d, r, c, nz))
        case _ A.Held{}:
          ad.mark_skip(m, d, c, A.Tk{hc, A.Held{}}, r, ad.cnt_mark(m, d, r, c, nz))
        case _ A.Preempted{}:
          ad.mark_skip(m, d, c, A.Tk{hc, A.Preempted{}}, r, ad.cnt_mark(m, d, r, c, nz))
        case _ A.Ended{}:
          ad.mark_skip(m, d, c, A.Tk{hc, A.Ended{}}, r, ad.cnt_mark(m, d, r, c, nz))

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

def ad.not_t(x: Bool, e: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      ad.absurd({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def ad.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def ad.bit_inj(b: Bool, -x: Nat, -y: Nat, e: {A.bit(b, x) == A.bit(b, y) : Nat}) -> {x == y : Nat}:
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

def ad.le_refl(n: Nat) -> {A.le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ad.le_refl(p)

def ad.zero2(a: Nat, b: Nat, e: {A.le(Nat.add(a, b), 0n) == True{} : Bool}) -> {a == 0n : Nat} & {b == 0n : Nat}:
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
def ad.mis(m: Maybe<&2, A.Cls>, c: A.Cls) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{d}:
      A.Cls.eq(d, c)

def ad.m_ia(-X: Type, -m: Maybe<&2, A.Cls>, e: {m == Some{A.Ia{}} : Maybe<&2, A.Cls>}, u: ad.BD(ad.mis(m, A.Ia{}), X, Unit)) -> X:
  %e : ad.BD(ad.mis(_, A.Ia{}), X, Unit)
  u

def ad.m_bg(-X: Type, -m: Maybe<&2, A.Cls>, e: {m == Some{A.Bg{}} : Maybe<&2, A.Cls>}, u: ad.BD(ad.mis(m, A.Bg{}), X, Unit)) -> X:
  %e : ad.BD(ad.mis(_, A.Bg{}), X, Unit)
  u

# The invariant: no lost wake-up, and background slots only while no
# interactive request holds or waits
# ------------------------------------------------------------------

def ad.ok.n(+l: A.Lim, +hi: Nat, +wi: Nat, +hb: Nat, +wb: Nat) -> Bool:
  Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, A.pick.go(A.room(l, Nat.add(hi, hb)), wi, hi, wb))), A.calm.n(hi, wi, hb))

def ad.ok(+l: A.Lim, +ts: List<&2, A.Tk>) -> Bool:
  ad.ok.n(l, A.cnt(A.Holding{}, A.Ia{}, ts), A.cnt(A.Waiting{}, A.Ia{}, ts), A.cnt(A.Holding{}, A.Bg{}, ts), A.cnt(A.Waiting{}, A.Bg{}, ts))

def ad.okS(s: A.St) -> Bool:
  match s:
    case A.St{+l, q, +ts}:
      ad.ok(l, ts)

def ad.ok.tr(-l: A.Lim, -a1: Nat, -a2: Nat, -a3: Nat, -a4: Nat, -b1: Nat, -b2: Nat, -b3: Nat, -b4: Nat, e1: {a1 == b1 : Nat}, e2: {a2 == b2 : Nat}, e3: {a3 == b3 : Nat}, e4: {a4 == b4 : Nat}, h: {ad.ok.n(l, a1, a2, a3, a4) == True{} : Bool}) -> {ad.ok.n(l, b1, b2, b3, b4) == True{} : Bool}:
  %e1 : {ad.ok.n(l, _, b2, b3, b4) == True{} : Bool}
  %e2 : {ad.ok.n(l, a1, _, b3, b4) == True{} : Bool}
  %e3 : {ad.ok.n(l, a1, a2, _, b4) == True{} : Bool}
  %e4 : {ad.ok.n(l, a1, a2, a3, _) == True{} : Bool}
  h

def ad.calm.tr(-a1: Nat, -a2: Nat, -a3: Nat, -b1: Nat, -b2: Nat, -b3: Nat, e1: {a1 == b1 : Nat}, e2: {a2 == b2 : Nat}, e3: {a3 == b3 : Nat}, h: {A.calm.n(a1, a2, a3) == True{} : Bool}) -> {A.calm.n(b1, b2, b3) == True{} : Bool}:
  %e1 : {A.calm.n(_, b2, b3) == True{} : Bool}
  %e2 : {A.calm.n(a1, _, b3) == True{} : Bool}
  %e3 : {A.calm.n(a1, a2, _) == True{} : Bool}
  h

def ad.pick_none0(r: Bool, hi: Nat) -> {A.pick.go(r, 0n, hi, 0n) == None{} : Maybe<&2, A.Cls>}:
  match r hi:
    case False{} _:
      {==}
    case True{} 0n:
      {==}
    case True{} 1n+x:
      {==}

def ad.pick_none_hi(r: Bool, -hi: Nat, -wb: Nat) -> {A.pick.go(r, 0n, 1n+hi, wb) == None{} : Maybe<&2, A.Cls>}:
  match r:
    case False{}:
      {==}
    case True{}:
      {==}

# with interactive slots held, background waiters do not matter
def ad.pick_hi(r: Bool, wi: Nat, -a: Nat, -x: Nat, -y: Nat) -> {A.pick.go(r, wi, 1n+a, x) == A.pick.go(r, wi, 1n+a, y) : Maybe<&2, A.Cls>}:
  match r wi:
    case False{} _:
      {==}
    case True{} 0n:
      {==}
    case True{} 1n+b:
      {==}

# with interactive waiters, background waiters do not matter
def ad.pick_wi(r: Bool, -b: Nat, -h: Nat, -x: Nat, -y: Nat) -> {A.pick.go(r, 1n+b, h, x) == A.pick.go(r, 1n+b, h, y) : Maybe<&2, A.Cls>}:
  match r:
    case False{}:
      {==}
    case True{}:
      {==}

def ad.pick_wb(r: Bool, -x: Nat, -y: Nat) -> {A.pick.go(r, 0n, 0n, 1n+x) == A.pick.go(r, 0n, 0n, 1n+y) : Maybe<&2, A.Cls>}:
  match r:
    case False{}:
      {==}
    case True{}:
      {==}

# a grant to an interactive waiter: one waits
def ad.pick_ia(r: Bool, wi: Nat, hi: Nat, wb: Nat, e: {A.pick.go(r, wi, hi, wb) == Some{A.Ia{}} : Maybe<&2, A.Cls>}) -> {A.isz(wi) == False{} : Bool}:
  match r wi hi wb:
    case False{} _ _ _:
      ad.m_ia({A.isz(wi) == False{} : Bool}, None{}, e, Unit{})
    case True{} 1n+a _ _:
      {==}
    case True{} 0n 1n+b _:
      ad.m_ia({A.isz(0n) == False{} : Bool}, None{}, e, Unit{})
    case True{} 0n 0n 0n:
      ad.m_ia({A.isz(0n) == False{} : Bool}, None{}, e, Unit{})
    case True{} 0n 0n 1n+d:
      ad.m_ia({A.isz(0n) == False{} : Bool}, Some{A.Bg{}}, e, Unit{})

# a grant to a background waiter: no interactive request holds or waits,
# and one background request waits
def ad.pick_bg(r: Bool, wi: Nat, hi: Nat, wb: Nat, e: {A.pick.go(r, wi, hi, wb) == Some{A.Bg{}} : Maybe<&2, A.Cls>}) -> {wi == 0n : Nat} & ({hi == 0n : Nat} & {A.isz(wb) == False{} : Bool}):
  match r wi hi wb:
    case False{} _ _ _:
      ad.m_bg({wi == 0n : Nat} & ({hi == 0n : Nat} & {A.isz(wb) == False{} : Bool}), None{}, e, Unit{})
    case True{} 1n+a _ _:
      ad.m_bg({1n+a == 0n : Nat} & ({hi == 0n : Nat} & {A.isz(wb) == False{} : Bool}), Some{A.Ia{}}, e, Unit{})
    case True{} 0n 1n+b _:
      ad.m_bg({0n == 0n : Nat} & ({1n+b == 0n : Nat} & {A.isz(wb) == False{} : Bool}), None{}, e, Unit{})
    case True{} 0n 0n 0n:
      ad.m_bg({0n == 0n : Nat} & ({0n == 0n : Nat} & {A.isz(0n) == False{} : Bool}), None{}, e, Unit{})
    case True{} 0n 0n 1n+d:
      ({==}, ({==}, {==}))

# calm stays calm as counts drop
def ad.calm_m1(-a: Nat, -b: Nat, c: Nat, h: {A.calm.n(1n+a, b, c) == True{} : Bool}) -> {A.calm.n(a, b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      ad.absurd({A.calm.n(a, b, 1n+x) == True{} : Bool}, h)

def ad.calm_m2(+a: Nat, -b: Nat, c: Nat, h: {A.calm.n(a, 1n+b, c) == True{} : Bool}) -> {A.calm.n(a, b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      ad.absurd({A.calm.n(a, b, 1n+x) == True{} : Bool}, Equal.trans(Bool, False{}, Bool.and(A.isz(a), False{}), True{}, Equal.sym(Bool, Bool.and(A.isz(a), False{}), False{}, ad.and_f(A.isz(a))), h))

def ad.calm_m3(-a: Nat, -b: Nat, c: Nat, h: {A.calm.n(a, b, 1n+c) == True{} : Bool}) -> {A.calm.n(a, b, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+x:
      h

def ad.calm_mono(x1: Bool, x2: Bool, x3: Bool, +a: Nat, +b: Nat, +c: Nat, h: {A.calm.n(A.bit(x1, a), A.bit(x2, b), A.bit(x3, c)) == True{} : Bool}) -> {A.calm.n(a, b, c) == True{} : Bool}:
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
def ad.calm_hb0(+hi: Nat, -w: Nat, hb: Nat, c: {A.calm.n(hi, 1n+w, hb) == True{} : Bool}) -> {hb == 0n : Nat}:
  match hb:
    case 0n:
      {==}
    case 1n+x:
      ad.absurd({1n+x == 0n : Nat}, Equal.trans(Bool, False{}, Bool.and(A.isz(hi), False{}), True{}, Equal.sym(Bool, Bool.and(A.isz(hi), False{}), False{}, ad.and_f(A.isz(hi))), c))

# an interactive waiter: no slot is free
def ad.ok_room(r: Bool, -w: Nat, -hi: Nat, -wb: Nat, -c: Bool, h: {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, A.pick.go(r, 1n+w, hi, wb))), c) == True{} : Bool}) -> {r == False{} : Bool}:
  match r:
    case True{}:
      ad.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# A grant keeps the invariant
# ---------------------------

def ad.ok_idle(+l: A.Lim, +hi: Nat, +hb: Nat, c: {A.calm.n(hi, 0n, hb) == True{} : Bool}) -> {ad.ok.n(l, hi, 0n, hb, 0n) == True{} : Bool}:
  +r = A.room(l, Nat.add(hi, hb))
  %Equal.sym(Maybe<&2, A.Cls>, A.pick.go(r, 0n, hi, 0n), None{}, ad.pick_none0(r, hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, _)), A.calm.n(hi, 0n, hb)) == True{} : Bool}
  c

def ad.grant_idle(+l: A.Lim, +t: List<&2, A.Tk>, z: {A.cnt(A.Waiting{}, A.Ia{}, t) == 0n : Nat} & {A.cnt(A.Waiting{}, A.Bg{}, t) == 0n : Nat}, cm: {A.calm(t) == True{} : Bool}) -> {ad.ok(l, t) == True{} : Bool}:
  (+zi, zb) = z
  +hi = A.cnt(A.Holding{}, A.Ia{}, t)
  +wi = A.cnt(A.Waiting{}, A.Ia{}, t)
  +hb = A.cnt(A.Holding{}, A.Bg{}, t)
  +wb = A.cnt(A.Waiting{}, A.Bg{}, t)
  ad.ok.tr(l, hi, 0n, hb, 0n, hi, wi, hb, wb, {==}, Equal.sym(Nat, wi, 0n, zi), {==}, Equal.sym(Nat, wb, 0n, zb), ad.ok_idle(l, hi, hb, ad.calm.tr(hi, wi, hb, hi, 0n, hb, {==}, zi, {==}, cm)))

def ad.not_none(-m: Maybe<&2, A.Cls>, e: {m == None{} : Maybe<&2, A.Cls>}) -> {Bool.not(Maybe.is_some(&2, A.Cls, m)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, A.Cls>, m, None{}, e) : {Bool.not(Maybe.is_some(&2, A.Cls, _)) == True{} : Bool}
  {==}

def ad.grant_none(+l: A.Lim, +t: List<&2, A.Tk>, ed: {A.pick(l, t) == None{} : Maybe<&2, A.Cls>}, cm: {A.calm(t) == True{} : Bool}) -> {ad.ok(l, t) == True{} : Bool}:
  +p = A.pick(l, t)
  ad.and_t(Bool.not(Maybe.is_some(&2, A.Cls, p)), A.calm(t), ad.not_none(p, ed), cm)

# the waiters bound the grants still to come
def ad.fuel_ia(+t: List<&2, A.Tk>, -f: Nat, +nz: {A.isz(A.cnt(A.Waiting{}, A.Ia{}, t)) == False{} : Bool}, fuel: {A.le(A.waits(t), 1n+f) == True{} : Bool}) -> {A.le(A.waits(A.mark(A.Ia{}, t)), f) == True{} : Bool}:
  +t2 = A.mark(A.Ia{}, t)
  +wi = A.cnt(A.Waiting{}, A.Ia{}, t)
  +wb = A.cnt(A.Waiting{}, A.Bg{}, t)
  +wi2 = A.cnt(A.Waiting{}, A.Ia{}, t2)
  +wb2 = A.cnt(A.Waiting{}, A.Bg{}, t2)
  %Equal.sym(Nat, wb2, wb, ad.cnt_mark(A.Waiting{}, A.Bg{}, t, A.Ia{}, nz)) : {A.le(Nat.add(wi2, _), f) == True{} : Bool}
  %Equal.sym(Nat, 1n+wi2, wi, ad.cnt_mark(A.Waiting{}, A.Ia{}, t, A.Ia{}, nz)) : {A.le(Nat.add(_, wb), 1n+f) == True{} : Bool}
  fuel

def ad.calm_ia(-a: Nat, -b: Nat, hb: Nat, +hi: Nat, -w: Nat, c: {A.calm.n(hi, 1n+w, hb) == True{} : Bool}) -> {A.calm.n(a, b, hb) == True{} : Bool}:
  match hb:
    case 0n:
      {==}
    case 1n+x:
      ad.absurd({A.calm.n(a, b, 1n+x) == True{} : Bool}, Equal.trans(Bool, False{}, Bool.and(A.isz(hi), False{}), True{}, Equal.sym(Bool, Bool.and(A.isz(hi), False{}), False{}, ad.and_f(A.isz(hi))), c))

def ad.calm_mark_ia(+t: List<&2, A.Tk>, +nz: {A.isz(A.cnt(A.Waiting{}, A.Ia{}, t)) == False{} : Bool}, cm: {A.calm(t) == True{} : Bool}) -> {A.calm(A.mark(A.Ia{}, t)) == True{} : Bool}:
  +t2 = A.mark(A.Ia{}, t)
  +hi = A.cnt(A.Holding{}, A.Ia{}, t)
  +wi = A.cnt(A.Waiting{}, A.Ia{}, t)
  +hb = A.cnt(A.Holding{}, A.Bg{}, t)
  +hi2 = A.cnt(A.Holding{}, A.Ia{}, t2)
  +wi2 = A.cnt(A.Waiting{}, A.Ia{}, t2)
  +hb2 = A.cnt(A.Holding{}, A.Bg{}, t2)
  %Equal.sym(Nat, hb2, hb, ad.cnt_mark(A.Holding{}, A.Bg{}, t, A.Ia{}, nz)) : {A.calm.n(hi2, wi2, _) == True{} : Bool}
  ad.calm_ia(hi2, wi2, hb, hi, wi2, ad.calm.tr(hi, wi, hb, hi, 1n+wi2, hb, {==}, Equal.sym(Nat, 1n+wi2, wi, ad.cnt_mark(A.Waiting{}, A.Ia{}, t, A.Ia{}, nz)), {==}, cm))

def ad.pbg(+l: A.Lim, +t: List<&2, A.Tk>, e: {A.pick(l, t) == Some{A.Bg{}} : Maybe<&2, A.Cls>}) -> {A.cnt(A.Waiting{}, A.Ia{}, t) == 0n : Nat} & ({A.cnt(A.Holding{}, A.Ia{}, t) == 0n : Nat} & {A.isz(A.cnt(A.Waiting{}, A.Bg{}, t)) == False{} : Bool}):
  ad.pick_bg(A.room(l, A.held(t)), A.cnt(A.Waiting{}, A.Ia{}, t), A.cnt(A.Holding{}, A.Ia{}, t), A.cnt(A.Waiting{}, A.Bg{}, t), e)

def ad.bg_wi(-t: List<&2, A.Tk>, p: {A.cnt(A.Waiting{}, A.Ia{}, t) == 0n : Nat} & ({A.cnt(A.Holding{}, A.Ia{}, t) == 0n : Nat} & {A.isz(A.cnt(A.Waiting{}, A.Bg{}, t)) == False{} : Bool})) -> {A.cnt(A.Waiting{}, A.Ia{}, t) == 0n : Nat}:
  (a, b, c) = p
  a

def ad.bg_hi(-t: List<&2, A.Tk>, p: {A.cnt(A.Waiting{}, A.Ia{}, t) == 0n : Nat} & ({A.cnt(A.Holding{}, A.Ia{}, t) == 0n : Nat} & {A.isz(A.cnt(A.Waiting{}, A.Bg{}, t)) == False{} : Bool})) -> {A.cnt(A.Holding{}, A.Ia{}, t) == 0n : Nat}:
  (a, b, c) = p
  b

def ad.bg_wb(-t: List<&2, A.Tk>, p: {A.cnt(A.Waiting{}, A.Ia{}, t) == 0n : Nat} & ({A.cnt(A.Holding{}, A.Ia{}, t) == 0n : Nat} & {A.isz(A.cnt(A.Waiting{}, A.Bg{}, t)) == False{} : Bool})) -> {A.isz(A.cnt(A.Waiting{}, A.Bg{}, t)) == False{} : Bool}:
  (a, b, c) = p
  c

def ad.fuel_bg(+t: List<&2, A.Tk>, -f: Nat, +zi: {A.cnt(A.Waiting{}, A.Ia{}, t) == 0n : Nat}, +nz: {A.isz(A.cnt(A.Waiting{}, A.Bg{}, t)) == False{} : Bool}, fuel: {A.le(A.waits(t), 1n+f) == True{} : Bool}) -> {A.le(A.waits(A.mark(A.Bg{}, t)), f) == True{} : Bool}:
  +t2 = A.mark(A.Bg{}, t)
  +wi = A.cnt(A.Waiting{}, A.Ia{}, t)
  +wb = A.cnt(A.Waiting{}, A.Bg{}, t)
  +wi2 = A.cnt(A.Waiting{}, A.Ia{}, t2)
  +wb2 = A.cnt(A.Waiting{}, A.Bg{}, t2)
  %Equal.sym(Nat, wi2, wi, ad.cnt_mark(A.Waiting{}, A.Ia{}, t, A.Bg{}, nz)) : {A.le(Nat.add(_, wb2), f) == True{} : Bool}
  %Equal.sym(Nat, wi, 0n, zi) : {A.le(Nat.add(_, wb2), f) == True{} : Bool}
  %Equal.sym(Nat, 1n+wb2, wb, ad.cnt_mark(A.Waiting{}, A.Bg{}, t, A.Bg{}, nz)) : {A.le(_, 1n+f) == True{} : Bool}
  %zi : {A.le(Nat.add(_, wb), 1n+f) == True{} : Bool}
  fuel

def ad.calm_bg(+t: List<&2, A.Tk>, zi: {A.cnt(A.Waiting{}, A.Ia{}, t) == 0n : Nat}, zh: {A.cnt(A.Holding{}, A.Ia{}, t) == 0n : Nat}, +nz: {A.isz(A.cnt(A.Waiting{}, A.Bg{}, t)) == False{} : Bool}) -> {A.calm(A.mark(A.Bg{}, t)) == True{} : Bool}:
  +t2 = A.mark(A.Bg{}, t)
  +hi = A.cnt(A.Holding{}, A.Ia{}, t)
  +wi = A.cnt(A.Waiting{}, A.Ia{}, t)
  +hi2 = A.cnt(A.Holding{}, A.Ia{}, t2)
  +wi2 = A.cnt(A.Waiting{}, A.Ia{}, t2)
  +hb2 = A.cnt(A.Holding{}, A.Bg{}, t2)
  %Equal.sym(Nat, hi2, hi, ad.cnt_mark(A.Holding{}, A.Ia{}, t, A.Bg{}, nz)) : {A.calm.n(_, wi2, hb2) == True{} : Bool}
  %Equal.sym(Nat, wi2, wi, ad.cnt_mark(A.Waiting{}, A.Ia{}, t, A.Bg{}, nz)) : {A.calm.n(hi, _, hb2) == True{} : Bool}
  %Equal.sym(Nat, hi, 0n, zh) : {A.calm.n(_, wi, hb2) == True{} : Bool}
  %Equal.sym(Nat, wi, 0n, zi) : {A.calm.n(0n, _, hb2) == True{} : Bool}
  ad.or_t(A.isz(hb2))

def ad.grant_ok(n: Nat, d: Maybe<&2, A.Cls>, +l: A.Lim, +t: List<&2, A.Tk>, +ed: {A.pick(l, t) == d : Maybe<&2, A.Cls>}, fuel: {A.le(A.waits(t), n) == True{} : Bool}, +cm: {A.calm(t) == True{} : Bool}) -> {ad.ok(l, A.grant.go(n, d, l, t)) == True{} : Bool}:
  match n d:
    case 0n _:
      ad.grant_idle(l, t, ad.zero2(A.cnt(A.Waiting{}, A.Ia{}, t), A.cnt(A.Waiting{}, A.Bg{}, t), fuel), cm)
    case 1n+f None{}:
      ad.grant_none(l, t, ed, cm)
    case 1n+f Some{A.Ia{}}:
      +nz = ad.pick_ia(A.room(l, A.held(t)), A.cnt(A.Waiting{}, A.Ia{}, t), A.cnt(A.Holding{}, A.Ia{}, t), A.cnt(A.Waiting{}, A.Bg{}, t), ed)
      ad.grant_ok(f, A.pick(l, A.mark(A.Ia{}, t)), l, A.mark(A.Ia{}, t), {==}, ad.fuel_ia(t, f, nz, fuel), ad.calm_mark_ia(t, nz, cm))
    case 1n+f Some{A.Bg{}}:
      ad.grant_ok(f, A.pick(l, A.mark(A.Bg{}, t)), l, A.mark(A.Bg{}, t), {==}, ad.fuel_bg(t, f, ad.bg_wi(t, ad.pbg(l, t, ed)), ad.bg_wb(t, ad.pbg(l, t, ed)), fuel), ad.calm_bg(t, ad.bg_wi(t, ad.pbg(l, t, ed)), ad.bg_hi(t, ad.pbg(l, t, ed)), ad.bg_wb(t, ad.pbg(l, t, ed))))

# Every op keeps the invariant
# ----------------------------

def ad.bit_off(-b: Bool, -x: Nat, off: {b == False{} : Bool}) -> {A.bit(b, x) == x : Nat}:
  %Equal.sym(Bool, b, False{}, off) : {A.bit(_, x) == x : Nat}
  {==}

# a ticket appended that the count does not see
def ad.app_off(+m: A.Mode, +c: A.Cls, +t: List<&2, A.Tk>, +x: A.Tk, off: {A.hit(m, c, x) == False{} : Bool}) -> {A.cnt(m, c, List.append(&2, A.Tk, t, [x])) == A.cnt(m, c, t) : Nat}:
  Equal.trans(Nat, A.cnt(m, c, List.append(&2, A.Tk, t, [x])), A.bit(A.hit(m, c, x), A.cnt(m, c, t)), A.cnt(m, c, t), ad.cnt_app(m, c, t, x), ad.bit_off(A.hit(m, c, x), A.cnt(m, c, t), off))

# an interactive ticket appended after a preemption
def ad.app_pre(+m: A.Mode, +ts: List<&2, A.Tk>, +x: A.Tk) -> {A.cnt(m, A.Ia{}, List.append(&2, A.Tk, A.preempt(ts), [x])) == A.bit(A.hit(m, A.Ia{}, x), A.cnt(m, A.Ia{}, ts)) : Nat}:
  +hx = A.hit(m, A.Ia{}, x)
  Equal.trans(Nat, A.cnt(m, A.Ia{}, List.append(&2, A.Tk, A.preempt(ts), [x])), A.bit(hx, A.cnt(m, A.Ia{}, A.preempt(ts))), A.bit(hx, A.cnt(m, A.Ia{}, ts)), ad.cnt_app(m, A.Ia{}, A.preempt(ts), x), Equal.cong(Nat, Nat, y => A.bit(hx, y), A.cnt(m, A.Ia{}, A.preempt(ts)), A.cnt(m, A.Ia{}, ts), ad.pre_ia(m, ts)))

def ad.put_at(+m: A.Mode, +cc: A.Cls, +ts: List<&2, A.Tk>, +k: Nat, +x: A.Sts, -mb: Maybe<&2, A.Tk>, e: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}) -> {A.bit(ad.at(m, cc, mb), A.cnt(m, cc, A.put(ts, k, x))) == A.bit(ad.at(m, cc, ad.set(mb, x)), A.cnt(m, cc, ts)) : Nat}:
  %e : {A.bit(ad.at(m, cc, _), A.cnt(m, cc, A.put(ts, k, x))) == A.bit(ad.at(m, cc, ad.set(_, x)), A.cnt(m, cc, ts)) : Nat}
  ad.cnt_put(m, cc, ts, k, x)

# collecting a granted permit changes no count
def ad.col_cnt(m: A.Mode, +cc: A.Cls, +ts: List<&2, A.Tk>, +k: Nat, +c: A.Cls, e: {A.get(ts, k) == Some{A.Tk{c, A.Granted{}}} : Maybe<&2, A.Tk>}) -> {A.cnt(m, cc, A.put(ts, k, A.Held{})) == A.cnt(m, cc, ts) : Nat}:
  match m:
    case A.Holding{}:
      ad.bit_inj(A.Cls.eq(cc, c), A.cnt(A.Holding{}, cc, A.put(ts, k, A.Held{})), A.cnt(A.Holding{}, cc, ts), ad.put_at(A.Holding{}, cc, ts, k, A.Held{}, Some{A.Tk{c, A.Granted{}}}, e))
    case A.Waiting{}:
      ad.put_at(A.Waiting{}, cc, ts, k, A.Held{}, Some{A.Tk{c, A.Granted{}}}, e)

# ending ticket k drops it from its count
def ad.end_cnt(m: A.Mode, +cc: A.Cls, +ts: List<&2, A.Tk>, +k: Nat, +c: A.Cls, +s: A.Sts, e: {A.get(ts, k) == Some{A.Tk{c, s}} : Maybe<&2, A.Tk>}) -> {A.bit(A.hit(m, cc, A.Tk{c, s}), A.cnt(m, cc, A.put(ts, k, A.Ended{}))) == A.cnt(m, cc, ts) : Nat}:
  match m:
    case A.Holding{}:
      ad.put_at(A.Holding{}, cc, ts, k, A.Ended{}, Some{A.Tk{c, s}}, e)
    case A.Waiting{}:
      ad.put_at(A.Waiting{}, cc, ts, k, A.Ended{}, Some{A.Tk{c, s}}, e)

def ad.end_calm(+ts: List<&2, A.Tk>, +k: Nat, +c: A.Cls, +s: A.Sts, +e: {A.get(ts, k) == Some{A.Tk{c, s}} : Maybe<&2, A.Tk>}, cm: {A.calm(ts) == True{} : Bool}) -> {A.calm(A.put(ts, k, A.Ended{})) == True{} : Bool}:
  +t2 = A.put(ts, k, A.Ended{})
  +x = {A.Tk{c, s} : A.Tk}
  +x1 = A.hit(A.Holding{}, A.Ia{}, x)
  +x2 = A.hit(A.Waiting{}, A.Ia{}, x)
  +x3 = A.hit(A.Holding{}, A.Bg{}, x)
  +a1 = A.cnt(A.Holding{}, A.Ia{}, t2)
  +a2 = A.cnt(A.Waiting{}, A.Ia{}, t2)
  +a3 = A.cnt(A.Holding{}, A.Bg{}, t2)
  ad.calm_mono(x1, x2, x3, a1, a2, a3, ad.calm.tr(A.cnt(A.Holding{}, A.Ia{}, ts), A.cnt(A.Waiting{}, A.Ia{}, ts), A.cnt(A.Holding{}, A.Bg{}, ts), A.bit(x1, a1), A.bit(x2, a2), A.bit(x3, a3), Equal.sym(Nat, A.bit(x1, a1), A.cnt(A.Holding{}, A.Ia{}, ts), ad.end_cnt(A.Holding{}, A.Ia{}, ts, k, c, s, e)), Equal.sym(Nat, A.bit(x2, a2), A.cnt(A.Waiting{}, A.Ia{}, ts), ad.end_cnt(A.Waiting{}, A.Ia{}, ts, k, c, s, e)), Equal.sym(Nat, A.bit(x3, a3), A.cnt(A.Holding{}, A.Bg{}, ts), ad.end_cnt(A.Holding{}, A.Bg{}, ts, k, c, s, e)), cm))

def ad.calm_of(+l: A.Lim, +ts: List<&2, A.Tk>, h: {ad.ok(l, ts) == True{} : Bool}) -> {A.calm(ts) == True{} : Bool}:
  ad.and_r(Bool.not(Maybe.is_some(&2, A.Cls, A.pick(l, ts))), A.calm(ts), h)

# a ticket ends, then the waiters are granted
def ad.end_grant(+l: A.Lim, +ts: List<&2, A.Tk>, +k: Nat, +c: A.Cls, +s: A.Sts, +e: {A.get(ts, k) == Some{A.Tk{c, s}} : Maybe<&2, A.Tk>}, cm: {A.calm(ts) == True{} : Bool}) -> {ad.ok(l, A.grant(l, A.put(ts, k, A.Ended{}))) == True{} : Bool}:
  +t2 = A.put(ts, k, A.Ended{})
  ad.grant_ok(A.waits(t2), A.pick(l, t2), l, t2, {==}, ad.le_refl(A.waits(t2)), ad.end_calm(ts, k, c, s, e, cm))

# an interactive admit: after the preemption a slot goes to it only
# while no interactive request waits; else no slot is free
def ad.adm_ia0(+l: A.Lim, +hi: Nat, +wb1: Nat, r: Bool, u: Bool, er: {A.room(l, hi) == r : Bool}) -> {ad.ok.n(l, A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(r, u)}), hi), A.bit(A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(r, u)}), 0n), 0n, wb1) == True{} : Bool}:
  match r u:
    case True{} _:
      +rr = A.room(l, Nat.add(1n+hi, 0n))
      %Equal.sym(Maybe<&2, A.Cls>, A.pick.go(rr, 0n, 1n+hi, wb1), None{}, ad.pick_none_hi(rr, hi, wb1)) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, _)), A.calm.n(1n+hi, 0n, 0n)) == True{} : Bool}
      {==}
    case False{} True{}:
      %Equal.sym(Nat, Nat.add(hi, 0n), hi, ad.add_zero(hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, A.pick.go(A.room(l, _), 0n, hi, wb1))), A.calm.n(hi, 0n, 0n)) == True{} : Bool}
      %Equal.sym(Bool, A.room(l, hi), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, A.pick.go(_, 0n, hi, wb1))), A.calm.n(hi, 0n, 0n)) == True{} : Bool}
      {==}
    case False{} False{}:
      %Equal.sym(Nat, Nat.add(hi, 0n), hi, ad.add_zero(hi)) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, A.pick.go(A.room(l, _), 1n, hi, wb1))), A.calm.n(hi, 1n, 0n)) == True{} : Bool}
      %Equal.sym(Bool, A.room(l, hi), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, A.pick.go(_, 1n, hi, wb1))), A.calm.n(hi, 1n, 0n)) == True{} : Bool}
      {==}

def ad.adm_ia1(+l: A.Lim, +hi: Nat, +w: Nat, +wb1: Nat, u: Bool, er: {A.room(l, Nat.add(hi, 0n)) == False{} : Bool}) -> {ad.ok.n(l, A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(False{}, u)}), hi), A.bit(A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(False{}, u)}), 1n+w), 0n, wb1) == True{} : Bool}:
  match u:
    case True{}:
      %Equal.sym(Bool, A.room(l, Nat.add(hi, 0n)), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, A.pick.go(_, 1n+w, hi, wb1))), A.calm.n(hi, 1n+w, 0n)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, A.room(l, Nat.add(hi, 0n)), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, A.pick.go(_, 2n+w, hi, wb1))), A.calm.n(hi, 2n+w, 0n)) == True{} : Bool}
      {==}

def ad.room0(+l: A.Lim, +hi: Nat, +w: Nat, +hb: Nat, +wb: Nat, +h: {ad.ok.n(l, hi, 1n+w, hb, wb) == True{} : Bool}) -> {A.room(l, Nat.add(hi, 0n)) == False{} : Bool}:
  +cn = A.calm.n(hi, 1n+w, hb)
  %ad.calm_hb0(hi, w, hb, ad.and_r(Bool.not(Maybe.is_some(&2, A.Cls, A.pick.go(A.room(l, Nat.add(hi, hb)), 1n+w, hi, wb))), cn, h)) : {A.room(l, Nat.add(hi, _)) == False{} : Bool}
  ad.ok_room(A.room(l, Nat.add(hi, hb)), w, hi, wb, cn, h)

def ad.adm_ia(+l: A.Lim, +q: Nat, +wi: Nat, +hi: Nat, +hb: Nat, +wb: Nat, +wb1: Nat, +h: {ad.ok.n(l, hi, wi, hb, wb) == True{} : Bool}) -> {ad.ok.n(l, A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(Bool.and(A.isz(wi), A.room(l, hi)), A.le(q, wi))}), hi), A.bit(A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(Bool.and(A.isz(wi), A.room(l, hi)), A.le(q, wi))}), wi), 0n, wb1) == True{} : Bool}:
  match wi:
    case 0n:
      ad.adm_ia0(l, hi, wb1, A.room(l, hi), A.le(q, 0n), {==})
    case 1n+w:
      ad.adm_ia1(l, hi, w, wb1, A.le(q, 1n+w), ad.room0(l, hi, w, hb, wb, h))

def ad.adm_ia_ok(+l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +h: {ad.ok(l, ts) == True{} : Bool}) -> {ad.ok(l, A.admit.ia(l, q, ts)) == True{} : Bool}:
  +hi = A.cnt(A.Holding{}, A.Ia{}, ts)
  +wi = A.cnt(A.Waiting{}, A.Ia{}, ts)
  +hb = A.cnt(A.Holding{}, A.Bg{}, ts)
  +wb = A.cnt(A.Waiting{}, A.Bg{}, ts)
  +st = A.admit.ia.st(Bool.and(A.isz(wi), A.room(l, hi)), A.le(q, wi))
  +x = {A.Tk{A.Ia{}, st} : A.Tk}
  +t1 = A.preempt(ts)
  +t2 = List.append(&2, A.Tk, t1, [x])
  ad.ok.tr(l, A.bit(A.hit(A.Holding{}, A.Ia{}, x), hi), A.bit(A.hit(A.Waiting{}, A.Ia{}, x), wi), 0n, A.cnt(A.Waiting{}, A.Bg{}, t1), A.cnt(A.Holding{}, A.Ia{}, t2), A.cnt(A.Waiting{}, A.Ia{}, t2), A.cnt(A.Holding{}, A.Bg{}, t2), A.cnt(A.Waiting{}, A.Bg{}, t2), Equal.sym(Nat, A.cnt(A.Holding{}, A.Ia{}, t2), A.bit(A.hit(A.Holding{}, A.Ia{}, x), hi), ad.app_pre(A.Holding{}, ts, x)), Equal.sym(Nat, A.cnt(A.Waiting{}, A.Ia{}, t2), A.bit(A.hit(A.Waiting{}, A.Ia{}, x), wi), ad.app_pre(A.Waiting{}, ts, x)), Equal.sym(Nat, A.cnt(A.Holding{}, A.Bg{}, t2), 0n, Equal.trans(Nat, A.cnt(A.Holding{}, A.Bg{}, t2), A.cnt(A.Holding{}, A.Bg{}, t1), 0n, ad.app_off(A.Holding{}, A.Bg{}, t1, x, ad.and_f(A.Mode.of(A.Holding{}, st))), ad.pre_hb(ts))), Equal.sym(Nat, A.cnt(A.Waiting{}, A.Bg{}, t2), A.cnt(A.Waiting{}, A.Bg{}, t1), ad.app_off(A.Waiting{}, A.Bg{}, t1, x, ad.and_f(A.Mode.of(A.Waiting{}, st)))), ad.adm_ia(l, q, wi, hi, hb, wb, A.cnt(A.Waiting{}, A.Bg{}, t1), h))

# a background admit: a slot only when no request holds one
# interactively or waits
def ad.adm_bg0(+l: A.Lim, +hb: Nat, r: Bool, er: {A.room(l, hb) == r : Bool}) -> {ad.ok.n(l, 0n, 0n, A.bit(A.hit(A.Holding{}, A.Bg{}, A.Tk{A.Bg{}, A.admit.bg.st(r)}), hb), A.bit(A.hit(A.Waiting{}, A.Bg{}, A.Tk{A.Bg{}, A.admit.bg.st(r)}), 0n)) == True{} : Bool}:
  match r:
    case True{}:
      +rr = A.room(l, 1n+hb)
      %Equal.sym(Maybe<&2, A.Cls>, A.pick.go(rr, 0n, 0n, 0n), None{}, ad.pick_none0(rr, 0n)) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, _)), A.calm.n(0n, 0n, 1n+hb)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, A.room(l, hb), False{}, er) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, A.pick.go(_, 0n, 0n, 1n))), A.calm.n(0n, 0n, hb)) == True{} : Bool}
      ad.or_t(A.isz(hb))

def ad.adm_bg(+l: A.Lim, +hi: Nat, +wi: Nat, +wb: Nat, +hb: Nat, h: {ad.ok.n(l, hi, wi, hb, wb) == True{} : Bool}) -> {ad.ok.n(l, hi, wi, A.bit(A.hit(A.Holding{}, A.Bg{}, A.Tk{A.Bg{}, A.admit.bg.st(Bool.and(A.isz(hi), Bool.and(A.isz(wi), Bool.and(A.isz(wb), A.room(l, Nat.add(hi, hb))))))}), hb), A.bit(A.hit(A.Waiting{}, A.Bg{}, A.Tk{A.Bg{}, A.admit.bg.st(Bool.and(A.isz(hi), Bool.and(A.isz(wi), Bool.and(A.isz(wb), A.room(l, Nat.add(hi, hb))))))}), wb)) == True{} : Bool}:
  match hi:
    case 1n+a:
      +rr = A.room(l, Nat.add(1n+a, hb))
      %ad.pick_hi(rr, wi, a, wb, 1n+wb) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, _)), A.calm.n(1n+a, wi, hb)) == True{} : Bool}
      h
    case 0n:
      match wi:
        case 1n+b:
          +rr = A.room(l, hb)
          %ad.pick_wi(rr, b, 0n, wb, 1n+wb) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, _)), A.calm.n(0n, 1n+b, hb)) == True{} : Bool}
          h
        case 0n:
          match wb:
            case 1n+c:
              +rr = A.room(l, hb)
              %ad.pick_wb(rr, c, 1n+c) : {Bool.and(Bool.not(Maybe.is_some(&2, A.Cls, _)), A.calm.n(0n, 0n, hb)) == True{} : Bool}
              h
            case 0n:
              ad.adm_bg0(l, hb, A.room(l, hb), {==})

def ad.adm_bg_ok(+l: A.Lim, +ts: List<&2, A.Tk>, h: {ad.ok(l, ts) == True{} : Bool}) -> {ad.ok(l, A.admit.bg(l, ts)) == True{} : Bool}:
  +hi = A.cnt(A.Holding{}, A.Ia{}, ts)
  +wi = A.cnt(A.Waiting{}, A.Ia{}, ts)
  +hb = A.cnt(A.Holding{}, A.Bg{}, ts)
  +wb = A.cnt(A.Waiting{}, A.Bg{}, ts)
  +st = A.admit.bg.st(Bool.and(A.isz(hi), Bool.and(A.isz(wi), Bool.and(A.isz(wb), A.room(l, Nat.add(hi, hb))))))
  +y = {A.Tk{A.Bg{}, st} : A.Tk}
  +t2 = List.append(&2, A.Tk, ts, [y])
  ad.ok.tr(l, hi, wi, A.bit(A.hit(A.Holding{}, A.Bg{}, y), hb), A.bit(A.hit(A.Waiting{}, A.Bg{}, y), wb), A.cnt(A.Holding{}, A.Ia{}, t2), A.cnt(A.Waiting{}, A.Ia{}, t2), A.cnt(A.Holding{}, A.Bg{}, t2), A.cnt(A.Waiting{}, A.Bg{}, t2), Equal.sym(Nat, A.cnt(A.Holding{}, A.Ia{}, t2), hi, ad.app_off(A.Holding{}, A.Ia{}, ts, y, ad.and_f(A.Mode.of(A.Holding{}, st)))), Equal.sym(Nat, A.cnt(A.Waiting{}, A.Ia{}, t2), wi, ad.app_off(A.Waiting{}, A.Ia{}, ts, y, ad.and_f(A.Mode.of(A.Waiting{}, st)))), Equal.sym(Nat, A.cnt(A.Holding{}, A.Bg{}, t2), A.bit(A.hit(A.Holding{}, A.Bg{}, y), hb), ad.cnt_app(A.Holding{}, A.Bg{}, ts, y)), Equal.sym(Nat, A.cnt(A.Waiting{}, A.Bg{}, t2), A.bit(A.hit(A.Waiting{}, A.Bg{}, y), wb), ad.cnt_app(A.Waiting{}, A.Bg{}, ts, y)), ad.adm_bg(l, hi, wi, wb, hb, h))

# the ticket ops, by the ticket's status
def ad.col_ok(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, +e: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}, h: {ad.ok(l, ts) == True{} : Bool}) -> {ad.okS(A.collect.at(mb, l, q, ts, k)) == True{} : Bool}:
  match mb:
    case None{}:
      h
    case Some{A.Tk{c, A.Queued{}}}:
      h
    case Some{A.Tk{+c, A.Granted{}}}:
      +t2 = A.put(ts, k, A.Held{})
      ad.ok.tr(l, A.cnt(A.Holding{}, A.Ia{}, ts), A.cnt(A.Waiting{}, A.Ia{}, ts), A.cnt(A.Holding{}, A.Bg{}, ts), A.cnt(A.Waiting{}, A.Bg{}, ts), A.cnt(A.Holding{}, A.Ia{}, t2), A.cnt(A.Waiting{}, A.Ia{}, t2), A.cnt(A.Holding{}, A.Bg{}, t2), A.cnt(A.Waiting{}, A.Bg{}, t2), Equal.sym(Nat, A.cnt(A.Holding{}, A.Ia{}, t2), A.cnt(A.Holding{}, A.Ia{}, ts), ad.col_cnt(A.Holding{}, A.Ia{}, ts, k, c, e)), Equal.sym(Nat, A.cnt(A.Waiting{}, A.Ia{}, t2), A.cnt(A.Waiting{}, A.Ia{}, ts), ad.col_cnt(A.Waiting{}, A.Ia{}, ts, k, c, e)), Equal.sym(Nat, A.cnt(A.Holding{}, A.Bg{}, t2), A.cnt(A.Holding{}, A.Bg{}, ts), ad.col_cnt(A.Holding{}, A.Bg{}, ts, k, c, e)), Equal.sym(Nat, A.cnt(A.Waiting{}, A.Bg{}, t2), A.cnt(A.Waiting{}, A.Bg{}, ts), ad.col_cnt(A.Waiting{}, A.Bg{}, ts, k, c, e)), h)
    case Some{A.Tk{c, A.Held{}}}:
      h
    case Some{A.Tk{c, A.Preempted{}}}:
      h
    case Some{A.Tk{c, A.Ended{}}}:
      h

def ad.rel_ok(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, +e: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}, +h: {ad.ok(l, ts) == True{} : Bool}) -> {ad.okS(A.release.at(mb, l, q, ts, k)) == True{} : Bool}:
  match mb:
    case None{}:
      h
    case Some{A.Tk{c, A.Queued{}}}:
      h
    case Some{A.Tk{c, A.Granted{}}}:
      h
    case Some{A.Tk{+c, A.Held{}}}:
      ad.end_grant(l, ts, k, c, A.Held{}, e, ad.calm_of(l, ts, h))
    case Some{A.Tk{+c, A.Preempted{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      ad.ok.tr(l, A.cnt(A.Holding{}, A.Ia{}, ts), A.cnt(A.Waiting{}, A.Ia{}, ts), A.cnt(A.Holding{}, A.Bg{}, ts), A.cnt(A.Waiting{}, A.Bg{}, ts), A.cnt(A.Holding{}, A.Ia{}, t2), A.cnt(A.Waiting{}, A.Ia{}, t2), A.cnt(A.Holding{}, A.Bg{}, t2), A.cnt(A.Waiting{}, A.Bg{}, t2), Equal.sym(Nat, A.cnt(A.Holding{}, A.Ia{}, t2), A.cnt(A.Holding{}, A.Ia{}, ts), ad.end_cnt(A.Holding{}, A.Ia{}, ts, k, c, A.Preempted{}, e)), Equal.sym(Nat, A.cnt(A.Waiting{}, A.Ia{}, t2), A.cnt(A.Waiting{}, A.Ia{}, ts), ad.end_cnt(A.Waiting{}, A.Ia{}, ts, k, c, A.Preempted{}, e)), Equal.sym(Nat, A.cnt(A.Holding{}, A.Bg{}, t2), A.cnt(A.Holding{}, A.Bg{}, ts), ad.end_cnt(A.Holding{}, A.Bg{}, ts, k, c, A.Preempted{}, e)), Equal.sym(Nat, A.cnt(A.Waiting{}, A.Bg{}, t2), A.cnt(A.Waiting{}, A.Bg{}, ts), ad.end_cnt(A.Waiting{}, A.Bg{}, ts, k, c, A.Preempted{}, e)), h)
    case Some{A.Tk{c, A.Ended{}}}:
      h

def ad.lea_ok(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, +e: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}, +h: {ad.ok(l, ts) == True{} : Bool}) -> {ad.okS(A.leave.at(mb, l, q, ts, k)) == True{} : Bool}:
  match mb:
    case None{}:
      h
    case Some{A.Tk{+c, A.Queued{}}}:
      ad.end_grant(l, ts, k, c, A.Queued{}, e, ad.calm_of(l, ts, h))
    case Some{A.Tk{+c, A.Granted{}}}:
      ad.end_grant(l, ts, k, c, A.Granted{}, e, ad.calm_of(l, ts, h))
    case Some{A.Tk{c, A.Held{}}}:
      h
    case Some{A.Tk{c, A.Preempted{}}}:
      h
    case Some{A.Tk{c, A.Ended{}}}:
      h

def ad.step_ok(s: A.St, o: A.Op, +h: {ad.okS(s) == True{} : Bool}) -> {ad.okS(A.step(s, o)) == True{} : Bool}:
  match s:
    case A.St{+l, +q, +ts}:
      match o:
        case A.Admit{A.Ia{}}:
          ad.adm_ia_ok(l, q, ts, h)
        case A.Admit{A.Bg{}}:
          ad.adm_bg_ok(l, ts, h)
        case A.Collect{+k}:
          ad.col_ok(A.get(ts, k), l, q, ts, k, {==}, h)
        case A.Release{+k}:
          ad.rel_ok(A.get(ts, k), l, q, ts, k, {==}, h)
        case A.Leave{+k}:
          ad.lea_ok(A.get(ts, k), l, q, ts, k, {==}, h)
        case A.Limit{+l2, q2}:
          ad.grant_ok(A.waits(ts), A.pick(l2, ts), l2, ts, {==}, ad.le_refl(A.waits(ts)), ad.calm_of(l, ts, h))

def ad.run_ok(os: List<&2, A.Op>, +s: A.St, h: {ad.okS(s) == True{} : Bool}) -> {ad.okS(A.run(os, s)) == True{} : Bool}:
  match os:
    case Nil{}:
      h
    case +o <> r:
      ad.run_ok(r, A.step(s, o), ad.step_ok(s, o, h))

def ad.new_ok(l: A.Lim, -q: Nat) -> {ad.okS(A.St.new(l, q)) == True{} : Bool}:
  match l:
    case A.Unl{}:
      {==}
    case A.Cap{p}:
      {==}

def ad.okS_quiet(s: A.St, h: {ad.okS(s) == True{} : Bool}) -> {A.grantable(s) == False{} : Bool}:
  match s:
    case A.St{+l, q, +ts}:
      +g = Maybe.is_some(&2, A.Cls, A.pick(l, ts))
      ad.not_t(g, ad.and_l(Bool.not(g), A.calm(ts), h))

def ad.okS_calm(s: A.St, h: {ad.okS(s) == True{} : Bool}) -> {A.calm(A.St.ts(s)) == True{} : Bool}:
  match s:
    case A.St{+l, q, +ts}:
      ad.calm_of(l, ts, h)

# Laws (a)-(c)
# ------------

def preempts(s: A.St) -> {A.cnt(A.Holding{}, A.Bg{}, A.St.ts(A.step(s, A.Admit{A.Ia{}}))) == 0n : Nat}:
  match s:
    case A.St{+l, +q, +ts}:
      +st = A.admit.ia.st(Bool.and(A.isz(A.cnt(A.Waiting{}, A.Ia{}, ts)), A.room(l, A.cnt(A.Holding{}, A.Ia{}, ts))), A.le(q, A.cnt(A.Waiting{}, A.Ia{}, ts)))
      +t1 = A.preempt(ts)
      Equal.trans(Nat, A.cnt(A.Holding{}, A.Bg{}, List.append(&2, A.Tk, t1, [A.Tk{A.Ia{}, st}])), A.cnt(A.Holding{}, A.Bg{}, t1), 0n, ad.app_off(A.Holding{}, A.Bg{}, t1, A.Tk{A.Ia{}, st}, ad.and_f(A.Mode.of(A.Holding{}, st))), ad.pre_hb(ts))

def no_lost_wakeup(+l: A.Lim, +q: Nat, +os: List<&2, A.Op>) -> {A.grantable(A.run(os, A.St.new(l, q))) == False{} : Bool}:
  ad.okS_quiet(A.run(os, A.St.new(l, q)), ad.run_ok(os, A.St.new(l, q), ad.new_ok(l, q)))

def background_yields(+l: A.Lim, +q: Nat, +os: List<&2, A.Op>) -> {A.calm(A.St.ts(A.run(os, A.St.new(l, q)))) == True{} : Bool}:
  ad.okS_calm(A.run(os, A.St.new(l, q)), ad.run_ok(os, A.St.new(l, q), ad.new_ok(l, q)))

# Every ticket ends exactly once
# ------------------------------

# a preemption ends no ticket and revives none
def ad.end_pre1(t: A.Tk) -> {A.ended(Some{A.Tk.preempt(t)}) == A.ended(Some{t}) : Bool}:
  match t:
    case A.Tk{A.Ia{}, s}:
      {==}
    case A.Tk{A.Bg{}, A.Queued{}}:
      {==}
    case A.Tk{A.Bg{}, A.Granted{}}:
      {==}
    case A.Tk{A.Bg{}, A.Held{}}:
      {==}
    case A.Tk{A.Bg{}, A.Preempted{}}:
      {==}
    case A.Tk{A.Bg{}, A.Ended{}}:
      {==}

def ad.end_pre(t: List<&2, A.Tk>, k: Nat) -> {A.ended(A.get(A.preempt(t), k)) == A.ended(A.get(t, k)) : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match k:
        case 0n:
          ad.end_pre1(h)
        case 1n+p:
          ad.end_pre(r, p)

def ad.end_app(t: List<&2, A.Tk>, -x: A.Tk, k: Nat, e: {A.ended(A.get(t, k)) == True{} : Bool}) -> {A.ended(A.get(List.append(&2, A.Tk, t, [x]), k)) == True{} : Bool}:
  match t:
    case Nil{}:
      ad.absurd({A.ended(A.get([x], k)) == True{} : Bool}, e)
    case +h <> +r:
      match k:
        case 0n:
          e
        case 1n+p:
          ad.end_app(r, x, p, e)

# a ticket op on another ticket leaves an ended one ended
def ad.end_put(t: List<&2, A.Tk>, k: Nat, j: Nat, -x: A.Sts, e: {A.ended(A.get(t, k)) == True{} : Bool}, ne: {A.ended(A.get(t, j)) == False{} : Bool}) -> {A.ended(A.get(A.put(t, j, x), k)) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case A.Tk{+c, +s} <> +r:
      match k j:
        case 0n 0n:
          ad.absurd({A.ended(Some{A.Tk{c, x}}) == True{} : Bool}, Equal.trans(Bool, False{}, A.ended(Some{A.Tk{c, s}}), True{}, Equal.sym(Bool, A.ended(Some{A.Tk{c, s}}), False{}, ne), e))
        case 0n 1n+q:
          e
        case 1n+p 0n:
          e
        case 1n+p 1n+q:
          ad.end_put(r, p, q, x, e, ne)

def ad.end_mark(t: List<&2, A.Tk>, +c: A.Cls, k: Nat, e: {A.ended(A.get(t, k)) == True{} : Bool}) -> {A.ended(A.get(A.mark(c, t), k)) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case A.Tk{+hc, +hs} <> +r:
      match hc hs:
        case A.Ia{} A.Queued{}:
          match c k:
            case A.Ia{} 0n:
              ad.absurd({A.ended(Some{A.Tk{A.Ia{}, A.Granted{}}}) == True{} : Bool}, e)
            case A.Ia{} 1n+p:
              e
            case A.Bg{} 0n:
              e
            case A.Bg{} 1n+p:
              ad.end_mark(r, A.Bg{}, p, e)
        case A.Bg{} A.Queued{}:
          match c k:
            case A.Bg{} 0n:
              ad.absurd({A.ended(Some{A.Tk{A.Bg{}, A.Granted{}}}) == True{} : Bool}, e)
            case A.Bg{} 1n+p:
              e
            case A.Ia{} 0n:
              e
            case A.Ia{} 1n+p:
              ad.end_mark(r, A.Ia{}, p, e)
        case _ A.Granted{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ A.Held{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ A.Preempted{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ A.Ended{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)

def ad.end_grant_k(n: Nat, d: Maybe<&2, A.Cls>, +l: A.Lim, +t: List<&2, A.Tk>, +k: Nat, e: {A.ended(A.get(t, k)) == True{} : Bool}) -> {A.ended(A.get(A.grant.go(n, d, l, t), k)) == True{} : Bool}:
  match n d:
    case 0n _:
      e
    case 1n+f None{}:
      e
    case 1n+f Some{+c}:
      ad.end_grant_k(f, A.pick(l, A.mark(c, t)), l, A.mark(c, t), k, ad.end_mark(t, c, k, e))

# ticket j, which is not ended, ends and the waiters are granted
def ad.ne_at(-ts: List<&2, A.Tk>, -j: Nat, -mb: Maybe<&2, A.Tk>, ej: {A.get(ts, j) == mb : Maybe<&2, A.Tk>}, f: {A.ended(mb) == False{} : Bool}) -> {A.ended(A.get(ts, j)) == False{} : Bool}:
  %Equal.sym(Maybe<&2, A.Tk>, A.get(ts, j), mb, ej) : {A.ended(_) == False{} : Bool}
  f

def ad.end_other(+l: A.Lim, +ts: List<&2, A.Tk>, +k: Nat, +j: Nat, -c: A.Cls, -s: A.Sts, ej: {A.get(ts, j) == Some{A.Tk{c, s}} : Maybe<&2, A.Tk>}, ne: {A.ended(Some{A.Tk{c, s}}) == False{} : Bool}, e: {A.ended(A.get(ts, k)) == True{} : Bool}) -> {A.ended(A.get(A.put(ts, j, A.Ended{}), k)) == True{} : Bool}:
  ad.end_put(ts, k, j, A.Ended{}, e, ad.ne_at(ts, j, Some{A.Tk{c, s}}, ej, ne))

def ad.end_col(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +j: Nat, +k: Nat, ej: {A.get(ts, j) == mb : Maybe<&2, A.Tk>}, e: {A.ended(A.get(ts, k)) == True{} : Bool}) -> {A.ended(A.status(A.collect.at(mb, l, q, ts, j), k)) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{A.Tk{c, A.Queued{}}}:
      e
    case Some{A.Tk{+c, A.Granted{}}}:
      ad.end_put(ts, k, j, A.Held{}, e, ad.ne_at(ts, j, Some{A.Tk{c, A.Granted{}}}, ej, {==}))
    case Some{A.Tk{c, A.Held{}}}:
      e
    case Some{A.Tk{c, A.Preempted{}}}:
      e
    case Some{A.Tk{c, A.Ended{}}}:
      e

def ad.end_rel(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +j: Nat, +k: Nat, ej: {A.get(ts, j) == mb : Maybe<&2, A.Tk>}, e: {A.ended(A.get(ts, k)) == True{} : Bool}) -> {A.ended(A.status(A.release.at(mb, l, q, ts, j), k)) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{A.Tk{c, A.Queued{}}}:
      e
    case Some{A.Tk{c, A.Granted{}}}:
      e
    case Some{A.Tk{+c, A.Held{}}}:
      +t2 = A.put(ts, j, A.Ended{})
      ad.end_grant_k(A.waits(t2), A.pick(l, t2), l, t2, k, ad.end_other(l, ts, k, j, c, A.Held{}, ej, {==}, e))
    case Some{A.Tk{+c, A.Preempted{}}}:
      ad.end_other(l, ts, k, j, c, A.Preempted{}, ej, {==}, e)
    case Some{A.Tk{c, A.Ended{}}}:
      e

def ad.end_lea(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +j: Nat, +k: Nat, ej: {A.get(ts, j) == mb : Maybe<&2, A.Tk>}, e: {A.ended(A.get(ts, k)) == True{} : Bool}) -> {A.ended(A.status(A.leave.at(mb, l, q, ts, j), k)) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{A.Tk{+c, A.Queued{}}}:
      +t2 = A.put(ts, j, A.Ended{})
      ad.end_grant_k(A.waits(t2), A.pick(l, t2), l, t2, k, ad.end_other(l, ts, k, j, c, A.Queued{}, ej, {==}, e))
    case Some{A.Tk{+c, A.Granted{}}}:
      +t2 = A.put(ts, j, A.Ended{})
      ad.end_grant_k(A.waits(t2), A.pick(l, t2), l, t2, k, ad.end_other(l, ts, k, j, c, A.Granted{}, ej, {==}, e))
    case Some{A.Tk{c, A.Held{}}}:
      e
    case Some{A.Tk{c, A.Preempted{}}}:
      e
    case Some{A.Tk{c, A.Ended{}}}:
      e

def ended_stays_ended(s: A.St, o: A.Op, +k: Nat, e: {A.ended(A.status(s, k)) == True{} : Bool}) -> {A.ended(A.status(A.step(s, o), k)) == True{} : Bool}:
  match s:
    case A.St{+l, +q, +ts}:
      match o:
        case A.Admit{A.Ia{}}:
          +st = A.admit.ia.st(Bool.and(A.isz(A.cnt(A.Waiting{}, A.Ia{}, ts)), A.room(l, A.cnt(A.Holding{}, A.Ia{}, ts))), A.le(q, A.cnt(A.Waiting{}, A.Ia{}, ts)))
          ad.end_app(A.preempt(ts), A.Tk{A.Ia{}, st}, k, Equal.trans(Bool, A.ended(A.get(A.preempt(ts), k)), A.ended(A.get(ts, k)), True{}, ad.end_pre(ts, k), e))
        case A.Admit{A.Bg{}}:
          +st = A.admit.bg.st(Bool.and(A.isz(A.cnt(A.Holding{}, A.Ia{}, ts)), Bool.and(A.isz(A.cnt(A.Waiting{}, A.Ia{}, ts)), Bool.and(A.isz(A.cnt(A.Waiting{}, A.Bg{}, ts)), A.room(l, A.held(ts))))))
          ad.end_app(ts, A.Tk{A.Bg{}, st}, k, e)
        case A.Collect{+j}:
          ad.end_col(A.get(ts, j), l, q, ts, j, k, {==}, e)
        case A.Release{+j}:
          ad.end_rel(A.get(ts, j), l, q, ts, j, k, {==}, e)
        case A.Leave{+j}:
          ad.end_lea(A.get(ts, j), l, q, ts, j, k, {==}, e)
        case A.Limit{+l2, q2}:
          ad.end_grant_k(A.waits(ts), A.pick(l2, ts), l2, ts, k, e)

# ending an ended ticket again changes nothing
def ad.twice(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, ej: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}, e: {A.ended(mb) == True{} : Bool}) -> {A.step(A.St{l, q, ts}, A.finish(mb, k)) == A.St{l, q, ts} : A.St}:
  match mb:
    case None{}:
      ad.absurd({A.step(A.St{l, q, ts}, A.Release{k}) == A.St{l, q, ts} : A.St}, e)
    case Some{A.Tk{c, A.Queued{}}}:
      ad.absurd({A.step(A.St{l, q, ts}, A.Leave{k}) == A.St{l, q, ts} : A.St}, e)
    case Some{A.Tk{c, A.Granted{}}}:
      ad.absurd({A.step(A.St{l, q, ts}, A.Leave{k}) == A.St{l, q, ts} : A.St}, e)
    case Some{A.Tk{c, A.Held{}}}:
      ad.absurd({A.step(A.St{l, q, ts}, A.Release{k}) == A.St{l, q, ts} : A.St}, e)
    case Some{A.Tk{c, A.Preempted{}}}:
      ad.absurd({A.step(A.St{l, q, ts}, A.Release{k}) == A.St{l, q, ts} : A.St}, e)
    case Some{A.Tk{+c, A.Ended{}}}:
      %Equal.sym(Maybe<&2, A.Tk>, A.get(ts, k), Some{A.Tk{c, A.Ended{}}}, ej) : {A.release.at(_, l, q, ts, k) == A.St{l, q, ts} : A.St}
      {==}

def end_twice_changes_nothing(s: A.St, +k: Nat, e: {A.ended(A.status(s, k)) == True{} : Bool}) -> {A.step(s, A.finish(A.status(s, k), k)) == s : A.St}:
  match s:
    case A.St{+l, +q, +ts}:
      ad.twice(A.get(ts, k), l, q, ts, k, {==}, e)

# ending a ticket ends it
def ad.end_self(t: List<&2, A.Tk>, k: Nat, live: {Maybe.is_some(&2, A.Tk, A.get(t, k)) == True{} : Bool}) -> {A.ended(A.get(A.put(t, k, A.Ended{}), k)) == True{} : Bool}:
  match t:
    case Nil{}:
      ad.absurd({A.ended(None{}) == True{} : Bool}, live)
    case A.Tk{c, s} <> +r:
      match k:
        case 0n:
          {==}
        case 1n+p:
          ad.end_self(r, p, live)

def ad.some_at(-ts: List<&2, A.Tk>, -k: Nat, -mb: Maybe<&2, A.Tk>, ej: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}, f: {Maybe.is_some(&2, A.Tk, mb) == True{} : Bool}) -> {Maybe.is_some(&2, A.Tk, A.get(ts, k)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, A.Tk>, A.get(ts, k), mb, ej) : {Maybe.is_some(&2, A.Tk, _) == True{} : Bool}
  f

def ad.ends(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, +ej: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}, live: {Maybe.is_some(&2, A.Tk, mb) == True{} : Bool}) -> {A.ended(A.status(A.step(A.St{l, q, ts}, A.finish(mb, k)), k)) == True{} : Bool}:
  match mb:
    case None{}:
      ad.absurd({A.ended(A.status(A.step(A.St{l, q, ts}, A.Release{k}), k)) == True{} : Bool}, live)
    case Some{A.Tk{+c, A.Queued{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      %Equal.sym(Maybe<&2, A.Tk>, A.get(ts, k), Some{A.Tk{c, A.Queued{}}}, ej) : {A.ended(A.get(A.St.ts(A.leave.at(_, l, q, ts, k)), k)) == True{} : Bool}
      ad.end_grant_k(A.waits(t2), A.pick(l, t2), l, t2, k, ad.end_self(ts, k, ad.some_at(ts, k, Some{A.Tk{c, A.Queued{}}}, ej, {==})))
    case Some{A.Tk{+c, A.Granted{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      %Equal.sym(Maybe<&2, A.Tk>, A.get(ts, k), Some{A.Tk{c, A.Granted{}}}, ej) : {A.ended(A.get(A.St.ts(A.leave.at(_, l, q, ts, k)), k)) == True{} : Bool}
      ad.end_grant_k(A.waits(t2), A.pick(l, t2), l, t2, k, ad.end_self(ts, k, ad.some_at(ts, k, Some{A.Tk{c, A.Granted{}}}, ej, {==})))
    case Some{A.Tk{+c, A.Held{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      %Equal.sym(Maybe<&2, A.Tk>, A.get(ts, k), Some{A.Tk{c, A.Held{}}}, ej) : {A.ended(A.get(A.St.ts(A.release.at(_, l, q, ts, k)), k)) == True{} : Bool}
      ad.end_grant_k(A.waits(t2), A.pick(l, t2), l, t2, k, ad.end_self(ts, k, ad.some_at(ts, k, Some{A.Tk{c, A.Held{}}}, ej, {==})))
    case Some{A.Tk{+c, A.Preempted{}}}:
      %Equal.sym(Maybe<&2, A.Tk>, A.get(ts, k), Some{A.Tk{c, A.Preempted{}}}, ej) : {A.ended(A.get(A.St.ts(A.release.at(_, l, q, ts, k)), k)) == True{} : Bool}
      ad.end_self(ts, k, ad.some_at(ts, k, Some{A.Tk{c, A.Preempted{}}}, ej, {==}))
    case Some{A.Tk{+c, A.Ended{}}}:
      %Equal.sym(Maybe<&2, A.Tk>, A.get(ts, k), Some{A.Tk{c, A.Ended{}}}, ej) : {A.ended(A.get(A.St.ts(A.release.at(_, l, q, ts, k)), k)) == True{} : Bool}
      %Equal.sym(Maybe<&2, A.Tk>, A.get(ts, k), Some{A.Tk{c, A.Ended{}}}, ej) : {A.ended(_) == True{} : Bool}
      {==}

def every_ticket_ends(s: A.St, +k: Nat, live: {Maybe.is_some(&2, A.Tk, A.status(s, k)) == True{} : Bool}) -> {A.ended(A.status(A.step(s, A.finish(A.status(s, k), k)), k)) == True{} : Bool}:
  match s:
    case A.St{+l, +q, +ts}:
      ad.ends(A.get(ts, k), l, q, ts, k, {==}, live)

# Slots held stay within the limit
# --------------------------------

def ad.le_trans(a: Nat, b: Nat, c: Nat, ab: {A.le(a, b) == True{} : Bool}, bc: {A.le(b, c) == True{} : Bool}) -> {A.le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      {==}
    case 1n+x 0n _:
      ad.absurd({A.le(1n+x, c) == True{} : Bool}, ab)
    case 1n+x 1n+y 0n:
      ad.absurd({A.le(1n+x, 0n) == True{} : Bool}, bc)
    case 1n+x 1n+y 1n+z:
      ad.le_trans(x, y, z, ab, bc)

def ad.add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ad.add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def ad.add_one(n: Nat) -> {1n+n == Nat.add(n, 1n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %ad.add_one(p) : {2n+p == 1n+_ : Nat}
      {==}

def ad.or_tl(x: Bool, -y: Bool, ex: {x == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      ad.absurd({Bool.or(False{}, y) == True{} : Bool}, ex)

def ad.or_elim(w: Bool, -v: Bool, ih: {Bool.or(w, v) == True{} : Bool}, f: {v == True{} : Bool} -> {w == True{} : Bool}) -> {w == True{} : Bool}:
  match w:
    case True{}:
      {==}
    case False{}:
      f(ih)

def ad.pick_room(r: Bool, -wi: Nat, -hi: Nat, -wb: Nat, -c: A.Cls, e: {A.pick.go(r, wi, hi, wb) == Some{c} : Maybe<&2, A.Cls>}) -> {r == True{} : Bool}:
  match r:
    case True{}:
      {==}
    case False{}:
      %e : ad.BD(Maybe.is_some(&2, A.Cls, _), {False{} == True{} : Bool}, Unit)
      Unit{}

def ad.within_room(l: A.Lim, -n: Nat, rm: {A.room(l, n) == True{} : Bool}) -> {A.within(l, 1n+n) == True{} : Bool}:
  match l:
    case A.Unl{}:
      {==}
    case A.Cap{p}:
      rm

def ad.within_of(l: A.Lim, +g: Nat, +m: Nat, lg: {A.le(g, 1n+m) == True{} : Bool}, rm: {A.room(l, m) == True{} : Bool}) -> {A.within(l, g) == True{} : Bool}:
  match l:
    case A.Unl{}:
      {==}
    case A.Cap{+p}:
      ad.le_trans(g, 1n+m, 1n+p, lg, rm)

# a grant takes one more slot
def ad.held_mark(+t: List<&2, A.Tk>, c: A.Cls, +nz: {A.isz(A.cnt(A.Waiting{}, c, t)) == False{} : Bool}) -> {A.held(A.mark(c, t)) == 1n+A.held(t) : Nat}:
  match c:
    case A.Ia{}:
      +hi = A.cnt(A.Holding{}, A.Ia{}, t)
      +hb = A.cnt(A.Holding{}, A.Bg{}, t)
      +t2 = A.mark(A.Ia{}, t)
      %Equal.sym(Nat, A.cnt(A.Holding{}, A.Ia{}, t2), 1n+hi, ad.cnt_mark(A.Holding{}, A.Ia{}, t, A.Ia{}, nz)) : {Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, t2)) == 1n+Nat.add(hi, hb) : Nat}
      %Equal.sym(Nat, A.cnt(A.Holding{}, A.Bg{}, t2), hb, ad.cnt_mark(A.Holding{}, A.Bg{}, t, A.Ia{}, nz)) : {Nat.add(1n+hi, _) == 1n+Nat.add(hi, hb) : Nat}
      {==}
    case A.Bg{}:
      +hi = A.cnt(A.Holding{}, A.Ia{}, t)
      +hb = A.cnt(A.Holding{}, A.Bg{}, t)
      +t2 = A.mark(A.Bg{}, t)
      %Equal.sym(Nat, A.cnt(A.Holding{}, A.Ia{}, t2), hi, ad.cnt_mark(A.Holding{}, A.Ia{}, t, A.Bg{}, nz)) : {Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, t2)) == 1n+Nat.add(hi, hb) : Nat}
      %Equal.sym(Nat, A.cnt(A.Holding{}, A.Bg{}, t2), 1n+hb, ad.cnt_mark(A.Holding{}, A.Bg{}, t, A.Bg{}, nz)) : {Nat.add(hi, _) == 1n+Nat.add(hi, hb) : Nat}
      Equal.sym(Nat, 1n+Nat.add(hi, hb), Nat.add(hi, 1n+hb), ad.add_succ(hi, hb))

def ad.nz_of(+l: A.Lim, +t: List<&2, A.Tk>, c: A.Cls, +ed: {A.pick(l, t) == Some{c} : Maybe<&2, A.Cls>}) -> {A.isz(A.cnt(A.Waiting{}, c, t)) == False{} : Bool}:
  match c:
    case A.Ia{}:
      ad.pick_ia(A.room(l, A.held(t)), A.cnt(A.Waiting{}, A.Ia{}, t), A.cnt(A.Holding{}, A.Ia{}, t), A.cnt(A.Waiting{}, A.Bg{}, t), ed)
    case A.Bg{}:
      ad.bg_wb(t, ad.pbg(l, t, ed))

def ad.cap_tr(-w: Bool, -g: Nat, -a: Nat, -b: Nat, e: {a == b : Nat}, ih: {Bool.or(w, A.le(g, a)) == True{} : Bool}) -> {Bool.or(w, A.le(g, b)) == True{} : Bool}:
  %e : {Bool.or(w, A.le(g, _)) == True{} : Bool}
  ih

def ad.cap_stay(+l: A.Lim, +t: List<&2, A.Tk>) -> {Bool.or(A.within(l, A.held(t)), A.le(A.held(t), A.held(t))) == True{} : Bool}:
  %Equal.sym(Bool, A.le(A.held(t), A.held(t)), True{}, ad.le_refl(A.held(t))) : {Bool.or(A.within(l, A.held(t)), _) == True{} : Bool}
  ad.or_t(A.within(l, A.held(t)))

# grants happen only into free slots
def ad.cap_grant(+n: Nat, +d: Maybe<&2, A.Cls>, +l: A.Lim, +t: List<&2, A.Tk>, +ed: {A.pick(l, t) == d : Maybe<&2, A.Cls>}) -> {Bool.or(A.within(l, A.held(A.grant.go(n, d, l, t))), A.le(A.held(A.grant.go(n, d, l, t)), A.held(t))) == True{} : Bool}:
  match n d:
    case 0n _:
      ad.cap_stay(l, t)
    case 1n+f None{}:
      ad.cap_stay(l, t)
    case 1n+f Some{+c}:
      +t2 = A.mark(c, t)
      +g = A.held(A.grant.go(f, A.pick(l, t2), l, t2))
      +w = A.within(l, g)
      +rm = ad.pick_room(A.room(l, A.held(t)), A.cnt(A.Waiting{}, A.Ia{}, t), A.cnt(A.Holding{}, A.Ia{}, t), A.cnt(A.Waiting{}, A.Bg{}, t), c, ed)
      +ih = ad.cap_tr(w, g, A.held(t2), 1n+A.held(t), ad.held_mark(t, c, ad.nz_of(l, t, c, ed)), ad.cap_grant(f, A.pick(l, t2), l, t2, {==}))
      ad.or_tl(w, A.le(g, A.held(t)), ad.or_elim(w, A.le(g, 1n+A.held(t)), ih, lg => ad.within_of(l, g, A.held(t), lg, rm)))

# Collected, released, left
def ad.held_col(+ts: List<&2, A.Tk>, +k: Nat, +c: A.Cls, +e: {A.get(ts, k) == Some{A.Tk{c, A.Granted{}}} : Maybe<&2, A.Tk>}) -> {A.held(A.put(ts, k, A.Held{})) == A.held(ts) : Nat}:
  +t2 = A.put(ts, k, A.Held{})
  %Equal.sym(Nat, A.cnt(A.Holding{}, A.Ia{}, t2), A.cnt(A.Holding{}, A.Ia{}, ts), ad.col_cnt(A.Holding{}, A.Ia{}, ts, k, c, e)) : {Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, t2)) == A.held(ts) : Nat}
  %Equal.sym(Nat, A.cnt(A.Holding{}, A.Bg{}, t2), A.cnt(A.Holding{}, A.Bg{}, ts), ad.col_cnt(A.Holding{}, A.Bg{}, ts, k, c, e)) : {Nat.add(A.cnt(A.Holding{}, A.Ia{}, ts), _) == A.held(ts) : Nat}
  {==}

# a ticket that holds no slot ends
def ad.held_same(+ts: List<&2, A.Tk>, +k: Nat, +c: A.Cls, s: A.Sts, +e: {A.get(ts, k) == Some{A.Tk{c, s}} : Maybe<&2, A.Tk>}, hs: {A.Mode.of(A.Holding{}, s) == False{} : Bool}) -> {A.held(A.put(ts, k, A.Ended{})) == A.held(ts) : Nat}:
  match s:
    case A.Queued{}:
      %ad.end_cnt(A.Holding{}, A.Ia{}, ts, k, c, A.Queued{}, e) : {Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, ts)) : Nat}
      %ad.end_cnt(A.Holding{}, A.Bg{}, ts, k, c, A.Queued{}, e) : {Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), _) : Nat}
      {==}
    case A.Granted{}:
      ad.absurd({A.held(A.put(ts, k, A.Ended{})) == A.held(ts) : Nat}, Equal.sym(Bool, True{}, False{}, hs))
    case A.Held{}:
      ad.absurd({A.held(A.put(ts, k, A.Ended{})) == A.held(ts) : Nat}, Equal.sym(Bool, True{}, False{}, hs))
    case A.Preempted{}:
      %ad.end_cnt(A.Holding{}, A.Ia{}, ts, k, c, A.Preempted{}, e) : {Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, ts)) : Nat}
      %ad.end_cnt(A.Holding{}, A.Bg{}, ts, k, c, A.Preempted{}, e) : {Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), _) : Nat}
      {==}
    case A.Ended{}:
      %ad.end_cnt(A.Holding{}, A.Ia{}, ts, k, c, A.Ended{}, e) : {Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, ts)) : Nat}
      %ad.end_cnt(A.Holding{}, A.Bg{}, ts, k, c, A.Ended{}, e) : {Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), _) : Nat}
      {==}

# a ticket that holds a slot ends: one slot frees
def ad.held_end(+ts: List<&2, A.Tk>, +k: Nat, c: A.Cls, s: A.Sts, +e: {A.get(ts, k) == Some{A.Tk{c, s}} : Maybe<&2, A.Tk>}, hs: {A.Mode.of(A.Holding{}, s) == True{} : Bool}) -> {1n+A.held(A.put(ts, k, A.Ended{})) == A.held(ts) : Nat}:
  match c s:
    case A.Ia{} A.Granted{}:
      %ad.end_cnt(A.Holding{}, A.Ia{}, ts, k, A.Ia{}, A.Granted{}, e) : {1n+Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, ts)) : Nat}
      %ad.end_cnt(A.Holding{}, A.Bg{}, ts, k, A.Ia{}, A.Granted{}, e) : {1n+Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(1n+A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), _) : Nat}
      {==}
    case A.Ia{} A.Held{}:
      %ad.end_cnt(A.Holding{}, A.Ia{}, ts, k, A.Ia{}, A.Held{}, e) : {1n+Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, ts)) : Nat}
      %ad.end_cnt(A.Holding{}, A.Bg{}, ts, k, A.Ia{}, A.Held{}, e) : {1n+Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(1n+A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), _) : Nat}
      {==}
    case A.Bg{} A.Granted{}:
      %ad.end_cnt(A.Holding{}, A.Ia{}, ts, k, A.Bg{}, A.Granted{}, e) : {1n+Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, ts)) : Nat}
      %ad.end_cnt(A.Holding{}, A.Bg{}, ts, k, A.Bg{}, A.Granted{}, e) : {1n+Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), _) : Nat}
      ad.add_succ(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{})))
    case A.Bg{} A.Held{}:
      %ad.end_cnt(A.Holding{}, A.Ia{}, ts, k, A.Bg{}, A.Held{}, e) : {1n+Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, ts)) : Nat}
      %ad.end_cnt(A.Holding{}, A.Bg{}, ts, k, A.Bg{}, A.Held{}, e) : {1n+Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{}))) == Nat.add(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), _) : Nat}
      ad.add_succ(A.cnt(A.Holding{}, A.Ia{}, A.put(ts, k, A.Ended{})), A.cnt(A.Holding{}, A.Bg{}, A.put(ts, k, A.Ended{})))
    case _ A.Queued{}:
      ad.absurd({1n+A.held(A.put(ts, k, A.Ended{})) == A.held(ts) : Nat}, hs)
    case _ A.Preempted{}:
      ad.absurd({1n+A.held(A.put(ts, k, A.Ended{})) == A.held(ts) : Nat}, hs)
    case _ A.Ended{}:
      ad.absurd({1n+A.held(A.put(ts, k, A.Ended{})) == A.held(ts) : Nat}, hs)

def ad.cap_id(+l: A.Lim, +n: Nat) -> {Bool.or(A.within(l, n), A.le(Nat.add(n, 0n), n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(n, 0n), n, ad.add_zero(n)) : {Bool.or(A.within(l, n), A.le(_, n)) == True{} : Bool}
  %Equal.sym(Bool, A.le(n, n), True{}, ad.le_refl(n)) : {Bool.or(A.within(l, n), _) == True{} : Bool}
  ad.or_t(A.within(l, n))

def ad.cap_add(-w: Bool, +g: Nat, +h: Nat, f: Nat, ih: {Bool.or(w, A.le(g, h)) == True{} : Bool}) -> {Bool.or(w, A.le(Nat.add(g, f), Nat.add(h, f))) == True{} : Bool}:
  match f:
    case 0n:
      %Equal.sym(Nat, Nat.add(g, 0n), g, ad.add_zero(g)) : {Bool.or(w, A.le(_, Nat.add(h, 0n))) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(h, 0n), h, ad.add_zero(h)) : {Bool.or(w, A.le(g, _)) == True{} : Bool}
      ih
    case 1n+p:
      %ad.add_succ(g, p) : {Bool.or(w, A.le(_, Nat.add(h, 1n+p))) == True{} : Bool}
      %ad.add_succ(h, p) : {Bool.or(w, A.le(1n+Nat.add(g, p), _)) == True{} : Bool}
      ad.cap_add(w, g, h, p, ih)

# a grant after an op that freed f slots
def ad.cap_after(+l: A.Lim, +t2: List<&2, A.Tk>, +ts: List<&2, A.Tk>, +f: Nat, e: {Nat.add(A.held(t2), f) == A.held(ts) : Nat}) -> {Bool.or(A.within(l, A.held(A.grant(l, t2))), A.le(Nat.add(A.held(A.grant(l, t2)), f), A.held(ts))) == True{} : Bool}:
  +g = A.held(A.grant(l, t2))
  %e : {Bool.or(A.within(l, g), A.le(Nat.add(g, f), _)) == True{} : Bool}
  ad.cap_add(A.within(l, g), g, A.held(t2), f, ad.cap_grant(A.waits(t2), A.pick(l, t2), l, t2, {==}))

def ad.cap_keep(+l: A.Lim, +hi: Nat, +hb: Nat) -> {Bool.or(A.within(l, Nat.add(hi, 0n)), A.le(Nat.add(Nat.add(hi, 0n), hb), Nat.add(hi, hb))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(hi, 0n), hi, ad.add_zero(hi)) : {Bool.or(A.within(l, _), A.le(Nat.add(_, hb), Nat.add(hi, hb))) == True{} : Bool}
  %Equal.sym(Bool, A.le(Nat.add(hi, hb), Nat.add(hi, hb)), True{}, ad.le_refl(Nat.add(hi, hb))) : {Bool.or(A.within(l, hi), _) == True{} : Bool}
  ad.or_t(A.within(l, hi))

def ad.room_z(-l: A.Lim, +hi: Nat, er: {A.room(l, hi) == True{} : Bool}) -> {A.room(l, Nat.add(hi, 0n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(hi, 0n), hi, ad.add_zero(hi)) : {A.room(l, _) == True{} : Bool}
  er

def ad.cap_ia0(+l: A.Lim, +hi: Nat, +hb: Nat, r: Bool, u: Bool, er: {A.room(l, hi) == r : Bool}) -> {Bool.or(A.within(l, Nat.add(A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(r, u)}), hi), 0n)), A.le(Nat.add(Nat.add(A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(r, u)}), hi), 0n), hb), Nat.add(hi, hb))) == True{} : Bool}:
  match r u:
    case True{} _:
      ad.or_tl(A.within(l, 1n+Nat.add(hi, 0n)), A.le(1n+Nat.add(Nat.add(hi, 0n), hb), Nat.add(hi, hb)), ad.within_room(l, Nat.add(hi, 0n), ad.room_z(l, hi, er)))
    case False{} True{}:
      ad.cap_keep(l, hi, hb)
    case False{} False{}:
      ad.cap_keep(l, hi, hb)

def ad.cap_ia1(+l: A.Lim, +hi: Nat, +hb: Nat, u: Bool) -> {Bool.or(A.within(l, Nat.add(A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(False{}, u)}), hi), 0n)), A.le(Nat.add(Nat.add(A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(False{}, u)}), hi), 0n), hb), Nat.add(hi, hb))) == True{} : Bool}:
  match u:
    case True{}:
      ad.cap_keep(l, hi, hb)
    case False{}:
      ad.cap_keep(l, hi, hb)

def ad.cap_ia(+l: A.Lim, +q: Nat, wi: Nat, +hi: Nat, +hb: Nat) -> {Bool.or(A.within(l, Nat.add(A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(Bool.and(A.isz(wi), A.room(l, hi)), A.le(q, wi))}), hi), 0n)), A.le(Nat.add(Nat.add(A.bit(A.hit(A.Holding{}, A.Ia{}, A.Tk{A.Ia{}, A.admit.ia.st(Bool.and(A.isz(wi), A.room(l, hi)), A.le(q, wi))}), hi), 0n), hb), Nat.add(hi, hb))) == True{} : Bool}:
  match wi:
    case 0n:
      ad.cap_ia0(l, hi, hb, A.room(l, hi), A.le(q, 0n), {==})
    case 1n+w:
      ad.cap_ia1(l, hi, hb, A.le(q, 1n+w))

def ad.cap_bg0(+l: A.Lim, +hb: Nat, r: Bool, er: {A.room(l, hb) == r : Bool}) -> {Bool.or(A.within(l, A.bit(A.hit(A.Holding{}, A.Bg{}, A.Tk{A.Bg{}, A.admit.bg.st(r)}), hb)), A.le(Nat.add(A.bit(A.hit(A.Holding{}, A.Bg{}, A.Tk{A.Bg{}, A.admit.bg.st(r)}), hb), 0n), hb)) == True{} : Bool}:
  match r:
    case True{}:
      ad.or_tl(A.within(l, 1n+hb), A.le(1n+Nat.add(hb, 0n), hb), ad.within_room(l, hb, er))
    case False{}:
      ad.cap_id(l, hb)

def ad.cap_bg(+l: A.Lim, hi: Nat, wi: Nat, wb: Nat, +hb: Nat) -> {Bool.or(A.within(l, Nat.add(hi, A.bit(A.hit(A.Holding{}, A.Bg{}, A.Tk{A.Bg{}, A.admit.bg.st(Bool.and(A.isz(hi), Bool.and(A.isz(wi), Bool.and(A.isz(wb), A.room(l, Nat.add(hi, hb))))))}), hb))), A.le(Nat.add(Nat.add(hi, A.bit(A.hit(A.Holding{}, A.Bg{}, A.Tk{A.Bg{}, A.admit.bg.st(Bool.and(A.isz(hi), Bool.and(A.isz(wi), Bool.and(A.isz(wb), A.room(l, Nat.add(hi, hb))))))}), hb)), 0n), Nat.add(hi, hb))) == True{} : Bool}:
  match hi:
    case 1n+a:
      ad.cap_id(l, Nat.add(1n+a, hb))
    case 0n:
      match wi:
        case 1n+b:
          ad.cap_id(l, hb)
        case 0n:
          match wb:
            case 1n+c:
              ad.cap_id(l, hb)
            case 0n:
              ad.cap_bg0(l, hb, A.room(l, hb), {==})

def ad.cap_col(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, e: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}) -> {Bool.or(A.within(A.St.lim(A.collect.at(mb, l, q, ts, k)), A.held(A.St.ts(A.collect.at(mb, l, q, ts, k)))), A.le(Nat.add(A.held(A.St.ts(A.collect.at(mb, l, q, ts, k))), 0n), A.held(ts))) == True{} : Bool}:
  match mb:
    case None{}:
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{c, A.Queued{}}}:
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{+c, A.Granted{}}}:
      +t2 = A.put(ts, k, A.Held{})
      %Equal.sym(Nat, A.held(t2), A.held(ts), ad.held_col(ts, k, c, e)) : {Bool.or(A.within(l, _), A.le(Nat.add(_, 0n), A.held(ts))) == True{} : Bool}
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{c, A.Held{}}}:
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{c, A.Preempted{}}}:
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{c, A.Ended{}}}:
      ad.cap_id(l, A.held(ts))

def ad.cap_rel(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, e: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}) -> {Bool.or(A.within(A.St.lim(A.release.at(mb, l, q, ts, k)), A.held(A.St.ts(A.release.at(mb, l, q, ts, k)))), A.le(Nat.add(A.held(A.St.ts(A.release.at(mb, l, q, ts, k))), A.freed.at(mb, True{})), A.held(ts))) == True{} : Bool}:
  match mb:
    case None{}:
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{c, A.Queued{}}}:
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{c, A.Granted{}}}:
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{+c, A.Held{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      ad.cap_after(l, t2, ts, 1n, Equal.trans(Nat, Nat.add(A.held(t2), 1n), 1n+A.held(t2), A.held(ts), Equal.sym(Nat, 1n+A.held(t2), Nat.add(A.held(t2), 1n), ad.add_one(A.held(t2))), ad.held_end(ts, k, c, A.Held{}, e, {==})))
    case Some{A.Tk{+c, A.Preempted{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      %Equal.sym(Nat, A.held(t2), A.held(ts), ad.held_same(ts, k, c, A.Preempted{}, e, {==})) : {Bool.or(A.within(l, _), A.le(Nat.add(_, 0n), A.held(ts))) == True{} : Bool}
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{c, A.Ended{}}}:
      ad.cap_id(l, A.held(ts))

def ad.cap_lea(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, e: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}) -> {Bool.or(A.within(A.St.lim(A.leave.at(mb, l, q, ts, k)), A.held(A.St.ts(A.leave.at(mb, l, q, ts, k)))), A.le(Nat.add(A.held(A.St.ts(A.leave.at(mb, l, q, ts, k))), A.freed.at(mb, False{})), A.held(ts))) == True{} : Bool}:
  match mb:
    case None{}:
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{+c, A.Queued{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      ad.cap_after(l, t2, ts, 0n, Equal.trans(Nat, Nat.add(A.held(t2), 0n), A.held(t2), A.held(ts), ad.add_zero(A.held(t2)), ad.held_same(ts, k, c, A.Queued{}, e, {==})))
    case Some{A.Tk{+c, A.Granted{}}}:
      +t2 = A.put(ts, k, A.Ended{})
      ad.cap_after(l, t2, ts, 1n, Equal.trans(Nat, Nat.add(A.held(t2), 1n), 1n+A.held(t2), A.held(ts), Equal.sym(Nat, 1n+A.held(t2), Nat.add(A.held(t2), 1n), ad.add_one(A.held(t2))), ad.held_end(ts, k, c, A.Granted{}, e, {==})))
    case Some{A.Tk{c, A.Held{}}}:
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{c, A.Preempted{}}}:
      ad.cap_id(l, A.held(ts))
    case Some{A.Tk{c, A.Ended{}}}:
      ad.cap_id(l, A.held(ts))

def capacity(s: A.St, o: A.Op) -> {Bool.or(A.within(A.St.lim(A.step(s, o)), A.held(A.St.ts(A.step(s, o)))), A.le(Nat.add(A.held(A.St.ts(A.step(s, o))), A.freed(s, o)), A.held(A.St.ts(s)))) == True{} : Bool}:
  match s:
    case A.St{+l, +q, +ts}:
      match o:
        case A.Admit{A.Ia{}}:
          +hi = A.cnt(A.Holding{}, A.Ia{}, ts)
          +wi = A.cnt(A.Waiting{}, A.Ia{}, ts)
          +hb = A.cnt(A.Holding{}, A.Bg{}, ts)
          +st = A.admit.ia.st(Bool.and(A.isz(wi), A.room(l, hi)), A.le(q, wi))
          +x = {A.Tk{A.Ia{}, st} : A.Tk}
          +t1 = A.preempt(ts)
          +t2 = List.append(&2, A.Tk, t1, [x])
          +b = A.bit(A.hit(A.Holding{}, A.Ia{}, x), hi)
          %Equal.sym(Nat, A.cnt(A.Holding{}, A.Ia{}, t2), b, ad.app_pre(A.Holding{}, ts, x)) : {Bool.or(A.within(l, Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, t2))), A.le(Nat.add(Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, t2)), hb), Nat.add(hi, hb))) == True{} : Bool}
          %Equal.sym(Nat, A.cnt(A.Holding{}, A.Bg{}, t2), 0n, Equal.trans(Nat, A.cnt(A.Holding{}, A.Bg{}, t2), A.cnt(A.Holding{}, A.Bg{}, t1), 0n, ad.app_off(A.Holding{}, A.Bg{}, t1, x, ad.and_f(A.Mode.of(A.Holding{}, st))), ad.pre_hb(ts))) : {Bool.or(A.within(l, Nat.add(b, _)), A.le(Nat.add(Nat.add(b, _), hb), Nat.add(hi, hb))) == True{} : Bool}
          ad.cap_ia(l, q, wi, hi, hb)
        case A.Admit{A.Bg{}}:
          +hi = A.cnt(A.Holding{}, A.Ia{}, ts)
          +wi = A.cnt(A.Waiting{}, A.Ia{}, ts)
          +hb = A.cnt(A.Holding{}, A.Bg{}, ts)
          +wb = A.cnt(A.Waiting{}, A.Bg{}, ts)
          +st = A.admit.bg.st(Bool.and(A.isz(hi), Bool.and(A.isz(wi), Bool.and(A.isz(wb), A.room(l, Nat.add(hi, hb))))))
          +y = {A.Tk{A.Bg{}, st} : A.Tk}
          +t2 = List.append(&2, A.Tk, ts, [y])
          +b = A.bit(A.hit(A.Holding{}, A.Bg{}, y), hb)
          %Equal.sym(Nat, A.cnt(A.Holding{}, A.Ia{}, t2), hi, ad.app_off(A.Holding{}, A.Ia{}, ts, y, ad.and_f(A.Mode.of(A.Holding{}, st)))) : {Bool.or(A.within(l, Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, t2))), A.le(Nat.add(Nat.add(_, A.cnt(A.Holding{}, A.Bg{}, t2)), 0n), Nat.add(hi, hb))) == True{} : Bool}
          %Equal.sym(Nat, A.cnt(A.Holding{}, A.Bg{}, t2), b, ad.cnt_app(A.Holding{}, A.Bg{}, ts, y)) : {Bool.or(A.within(l, Nat.add(hi, _)), A.le(Nat.add(Nat.add(hi, _), 0n), Nat.add(hi, hb))) == True{} : Bool}
          ad.cap_bg(l, hi, wi, wb, hb)
        case A.Collect{+k}:
          ad.cap_col(A.get(ts, k), l, q, ts, k, {==})
        case A.Release{+k}:
          ad.cap_rel(A.get(ts, k), l, q, ts, k, {==})
        case A.Leave{+k}:
          ad.cap_lea(A.get(ts, k), l, q, ts, k, {==})
        case A.Limit{+l2, q2}:
          ad.cap_after(l2, ts, ts, 0n, ad.add_zero(A.held(ts)))

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
def ad.f_any(t: List<&2, A.Tk>, +c: A.Cls, b: Bool, e: {A.fifo(c, t, True{}) == True{} : Bool}) -> {A.fifo(c, t, b) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match b:
        case True{}:
          e
        case False{}:
          ad.f_any(r, c, A.hit(A.Waiting{}, c, h), ad.and_r(Bool.not(A.hit(A.Holding{}, c, h)), A.fifo(c, r, True{}), e))

def ad.f_weak(+r: List<&2, A.Tk>, +c: A.Cls, s: Bool, w: Bool, e: {A.fifo(c, r, Bool.or(s, w)) == True{} : Bool}) -> {A.fifo(c, r, s) == True{} : Bool}:
  match s:
    case True{}:
      e
    case False{}:
      match w:
        case True{}:
          ad.f_any(r, c, False{}, e)
        case False{}:
          e

def ad.f_pre_ia(t: List<&2, A.Tk>, +s: Bool) -> {A.fifo(A.Ia{}, A.preempt(t), s) == A.fifo(A.Ia{}, t, s) : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      +hh = A.hit(A.Holding{}, A.Ia{}, h)
      +hw = A.hit(A.Waiting{}, A.Ia{}, h)
      +rhs = Bool.and(Bool.not(Bool.and(s, hh)), A.fifo(A.Ia{}, r, Bool.or(s, hw)))
      %Equal.sym(Bool, A.hit(A.Holding{}, A.Ia{}, A.Tk.preempt(h)), hh, ad.hit_pre(A.Holding{}, h)) : {Bool.and(Bool.not(Bool.and(s, _)), A.fifo(A.Ia{}, A.preempt(r), Bool.or(s, A.hit(A.Waiting{}, A.Ia{}, A.Tk.preempt(h))))) == rhs : Bool}
      %Equal.sym(Bool, A.hit(A.Waiting{}, A.Ia{}, A.Tk.preempt(h)), hw, ad.hit_pre(A.Waiting{}, h)) : {Bool.and(Bool.not(Bool.and(s, hh)), A.fifo(A.Ia{}, A.preempt(r), Bool.or(s, _))) == rhs : Bool}
      %Equal.sym(Bool, A.fifo(A.Ia{}, A.preempt(r), Bool.or(s, hw)), A.fifo(A.Ia{}, r, Bool.or(s, hw)), ad.f_pre_ia(r, Bool.or(s, hw))) : {Bool.and(Bool.not(Bool.and(s, hh)), _) == rhs : Bool}
      {==}

def ad.f_pre_bg(t: List<&2, A.Tk>, +s: Bool) -> {A.fifo(A.Bg{}, A.preempt(t), s) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      +rest = A.fifo(A.Bg{}, A.preempt(r), Bool.or(s, A.hit(A.Waiting{}, A.Bg{}, A.Tk.preempt(h))))
      %Equal.sym(Bool, A.hit(A.Holding{}, A.Bg{}, A.Tk.preempt(h)), False{}, ad.hb_pre(h)) : {Bool.and(Bool.not(Bool.and(s, _)), rest) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(s, False{}), False{}, ad.and_f(s)) : {Bool.and(Bool.not(_), rest) == True{} : Bool}
      ad.f_pre_bg(r, Bool.or(s, A.hit(A.Waiting{}, A.Bg{}, A.Tk.preempt(h))))

def ad.fapp0(s: Bool, x: Bool, ok: {Bool.or(Bool.not(x), Bool.and(Bool.not(s), True{})) == True{} : Bool}) -> {Bool.and(Bool.not(Bool.and(s, x)), True{}) == True{} : Bool}:
  match s x:
    case True{} True{}:
      ad.absurd({False{} == True{} : Bool}, ok)
    case True{} False{}:
      {==}
    case False{} _:
      {==}

def ad.fapp_ok(x: Bool, s: Bool, w: Bool, n: Nat, ok: {Bool.or(Bool.not(x), Bool.and(Bool.not(s), A.isz(A.bit(w, n)))) == True{} : Bool}) -> {Bool.or(Bool.not(x), Bool.and(Bool.not(Bool.or(s, w)), A.isz(n))) == True{} : Bool}:
  match x s w:
    case False{} _ _:
      {==}
    case True{} True{} _:
      ad.absurd({Bool.or(False{}, Bool.and(False{}, A.isz(n))) == True{} : Bool}, ok)
    case True{} False{} True{}:
      ad.absurd({Bool.or(False{}, Bool.and(False{}, A.isz(n))) == True{} : Bool}, ok)
    case True{} False{} False{}:
      ok

# a ticket appended keeps the order, if it takes no slot while an older
# one of its class waits
def ad.f_app(t: List<&2, A.Tk>, +c: A.Cls, +s: Bool, +x: A.Tk, +e: {A.fifo(c, t, s) == True{} : Bool}, ok: {Bool.or(Bool.not(A.hit(A.Holding{}, c, x)), Bool.and(Bool.not(s), A.isz(A.cnt(A.Waiting{}, c, t)))) == True{} : Bool}) -> {A.fifo(c, List.append(&2, A.Tk, t, [x]), s) == True{} : Bool}:
  match t:
    case Nil{}:
      ad.fapp0(s, A.hit(A.Holding{}, c, x), ok)
    case +h <> +r:
      +hh = A.hit(A.Holding{}, c, h)
      +hw = A.hit(A.Waiting{}, c, h)
      ad.and_t(Bool.not(Bool.and(s, hh)), A.fifo(c, List.append(&2, A.Tk, r, [x]), Bool.or(s, hw)), ad.and_l(Bool.not(Bool.and(s, hh)), A.fifo(c, r, Bool.or(s, hw)), e), ad.f_app(r, c, Bool.or(s, hw), x, ad.and_r(Bool.not(Bool.and(s, hh)), A.fifo(c, r, Bool.or(s, hw)), e), ad.fapp_ok(A.hit(A.Holding{}, c, x), s, hw, A.cnt(A.Waiting{}, c, r), ok)))

# a ticket that ends keeps the order
def ad.f_end(t: List<&2, A.Tk>, +c: A.Cls, +s: Bool, k: Nat, +e: {A.fifo(c, t, s) == True{} : Bool}) -> {A.fifo(c, A.put(t, k, A.Ended{}), s) == True{} : Bool}:
  match t k:
    case Nil{} _:
      e
    case A.Tk{+hc, +hs} <> +r 0n:
      +hh = A.hit(A.Holding{}, c, A.Tk{hc, hs})
      +hw = A.hit(A.Waiting{}, c, A.Tk{hc, hs})
      %Equal.sym(Bool, Bool.and(s, False{}), False{}, ad.and_f(s)) : {Bool.and(Bool.not(_), A.fifo(c, r, Bool.or(s, False{}))) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(s, False{}), s, ad.or_f(s)) : {A.fifo(c, r, _) == True{} : Bool}
      ad.f_weak(r, c, s, hw, ad.and_r(Bool.not(Bool.and(s, hh)), A.fifo(c, r, Bool.or(s, hw)), e))
    case A.Tk{+hc, +hs} <> +r 1n+p:
      +hh = A.hit(A.Holding{}, c, A.Tk{hc, hs})
      +hw = A.hit(A.Waiting{}, c, A.Tk{hc, hs})
      ad.and_t(Bool.not(Bool.and(s, hh)), A.fifo(c, A.put(r, p, A.Ended{}), Bool.or(s, hw)), ad.and_l(Bool.not(Bool.and(s, hh)), A.fifo(c, r, Bool.or(s, hw)), e), ad.f_end(r, c, Bool.or(s, hw), p, ad.and_r(Bool.not(Bool.and(s, hh)), A.fifo(c, r, Bool.or(s, hw)), e)))

def ad.isg(m: Maybe<&2, A.Tk>) -> Bool:
  match m:
    case Some{A.Tk{c, A.Granted{}}}:
      True{}
    case _:
      False{}

def ad.fcol0(+hc: A.Cls, hs: A.Sts, +r: List<&2, A.Tk>, +c: A.Cls, +s: Bool, e: {A.fifo(c, A.Tk{hc, hs} <> r, s) == True{} : Bool}, g: {ad.isg(Some{A.Tk{hc, hs}}) == True{} : Bool}) -> {A.fifo(c, A.Tk{hc, A.Held{}} <> r, s) == True{} : Bool}:
  match hs:
    case A.Queued{}:
      ad.absurd({A.fifo(c, A.Tk{hc, A.Held{}} <> r, s) == True{} : Bool}, g)
    case A.Granted{}:
      e
    case A.Held{}:
      ad.absurd({A.fifo(c, A.Tk{hc, A.Held{}} <> r, s) == True{} : Bool}, g)
    case A.Preempted{}:
      ad.absurd({A.fifo(c, A.Tk{hc, A.Held{}} <> r, s) == True{} : Bool}, g)
    case A.Ended{}:
      ad.absurd({A.fifo(c, A.Tk{hc, A.Held{}} <> r, s) == True{} : Bool}, g)

# collecting a grant keeps the order
def ad.f_col(t: List<&2, A.Tk>, +c: A.Cls, +s: Bool, k: Nat, +e: {A.fifo(c, t, s) == True{} : Bool}, g: {ad.isg(A.get(t, k)) == True{} : Bool}) -> {A.fifo(c, A.put(t, k, A.Held{}), s) == True{} : Bool}:
  match t k:
    case Nil{} _:
      e
    case A.Tk{+hc, +hs} <> +r 0n:
      ad.fcol0(hc, hs, r, c, s, e, g)
    case A.Tk{+hc, +hs} <> +r 1n+p:
      +hh = A.hit(A.Holding{}, c, A.Tk{hc, hs})
      +hw = A.hit(A.Waiting{}, c, A.Tk{hc, hs})
      ad.and_t(Bool.not(Bool.and(s, hh)), A.fifo(c, A.put(r, p, A.Held{}), Bool.or(s, hw)), ad.and_l(Bool.not(Bool.and(s, hh)), A.fifo(c, r, Bool.or(s, hw)), e), ad.f_col(r, c, Bool.or(s, hw), p, ad.and_r(Bool.not(Bool.and(s, hh)), A.fifo(c, r, Bool.or(s, hw)), e), g))

# a grant to class c takes its oldest waiter
def ad.f_mark(t: List<&2, A.Tk>, +c: A.Cls, e: {A.fifo(c, t, False{}) == True{} : Bool}) -> {A.fifo(c, A.mark(c, t), False{}) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case A.Tk{+hc, +hs} <> +r:
      match hc hs:
        case A.Ia{} A.Queued{}:
          match c:
            case A.Ia{}:
              ad.f_any(r, A.Ia{}, False{}, e)
            case A.Bg{}:
              ad.f_mark(r, A.Bg{}, e)
        case A.Bg{} A.Queued{}:
          match c:
            case A.Ia{}:
              ad.f_mark(r, A.Ia{}, e)
            case A.Bg{}:
              ad.f_any(r, A.Bg{}, False{}, e)
        case _ A.Granted{}:
          ad.f_mark(r, c, e)
        case _ A.Held{}:
          ad.f_mark(r, c, e)
        case _ A.Preempted{}:
          ad.f_mark(r, c, e)
        case _ A.Ended{}:
          ad.f_mark(r, c, e)

# a grant to the other class keeps the order: (c, d) is (Ia, Bg) or
# (Bg, Ia)
def ad.f_tail(+c: A.Cls, +h: A.Tk, -r: List<&2, A.Tk>, +s: Bool, e: {A.fifo(c, h <> r, s) == True{} : Bool}) -> {A.fifo(c, r, Bool.or(s, A.hit(A.Waiting{}, c, h))) == True{} : Bool}:
  ad.and_r(Bool.not(Bool.and(s, A.hit(A.Holding{}, c, h))), A.fifo(c, r, Bool.or(s, A.hit(A.Waiting{}, c, h))), e)

def ad.f_skip(+c: A.Cls, +h: A.Tk, -r2: List<&2, A.Tk>, -r: List<&2, A.Tk>, +s: Bool, e: {A.fifo(c, h <> r, s) == True{} : Bool}, ih: {A.fifo(c, r2, Bool.or(s, A.hit(A.Waiting{}, c, h))) == True{} : Bool}) -> {A.fifo(c, h <> r2, s) == True{} : Bool}:
  ad.and_t(Bool.not(Bool.and(s, A.hit(A.Holding{}, c, h))), A.fifo(c, r2, Bool.or(s, A.hit(A.Waiting{}, c, h))), ad.and_l(Bool.not(Bool.and(s, A.hit(A.Holding{}, c, h))), A.fifo(c, r, Bool.or(s, A.hit(A.Waiting{}, c, h))), e), ih)

def ad.f_mark_ib(t: List<&2, A.Tk>, +s: Bool, +e: {A.fifo(A.Ia{}, t, s) == True{} : Bool}) -> {A.fifo(A.Ia{}, A.mark(A.Bg{}, t), s) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case A.Tk{+hc, +hs} <> +r:
      match hc hs:
        case A.Bg{} A.Queued{}:
          e
        case A.Ia{} A.Queued{}:
          ad.f_skip(A.Ia{}, A.Tk{A.Ia{}, A.Queued{}}, A.mark(A.Bg{}, r), r, s, e, ad.f_mark_ib(r, Bool.or(s, A.hit(A.Waiting{}, A.Ia{}, A.Tk{A.Ia{}, A.Queued{}})), ad.f_tail(A.Ia{}, A.Tk{A.Ia{}, A.Queued{}}, r, s, e)))
        case _ A.Granted{}:
          ad.f_skip(A.Ia{}, A.Tk{hc, A.Granted{}}, A.mark(A.Bg{}, r), r, s, e, ad.f_mark_ib(r, Bool.or(s, A.hit(A.Waiting{}, A.Ia{}, A.Tk{hc, A.Granted{}})), ad.f_tail(A.Ia{}, A.Tk{hc, A.Granted{}}, r, s, e)))
        case _ A.Held{}:
          ad.f_skip(A.Ia{}, A.Tk{hc, A.Held{}}, A.mark(A.Bg{}, r), r, s, e, ad.f_mark_ib(r, Bool.or(s, A.hit(A.Waiting{}, A.Ia{}, A.Tk{hc, A.Held{}})), ad.f_tail(A.Ia{}, A.Tk{hc, A.Held{}}, r, s, e)))
        case _ A.Preempted{}:
          ad.f_skip(A.Ia{}, A.Tk{hc, A.Preempted{}}, A.mark(A.Bg{}, r), r, s, e, ad.f_mark_ib(r, Bool.or(s, A.hit(A.Waiting{}, A.Ia{}, A.Tk{hc, A.Preempted{}})), ad.f_tail(A.Ia{}, A.Tk{hc, A.Preempted{}}, r, s, e)))
        case _ A.Ended{}:
          ad.f_skip(A.Ia{}, A.Tk{hc, A.Ended{}}, A.mark(A.Bg{}, r), r, s, e, ad.f_mark_ib(r, Bool.or(s, A.hit(A.Waiting{}, A.Ia{}, A.Tk{hc, A.Ended{}})), ad.f_tail(A.Ia{}, A.Tk{hc, A.Ended{}}, r, s, e)))

def ad.f_mark_bi(t: List<&2, A.Tk>, +s: Bool, +e: {A.fifo(A.Bg{}, t, s) == True{} : Bool}) -> {A.fifo(A.Bg{}, A.mark(A.Ia{}, t), s) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case A.Tk{+hc, +hs} <> +r:
      match hc hs:
        case A.Ia{} A.Queued{}:
          e
        case A.Bg{} A.Queued{}:
          ad.f_skip(A.Bg{}, A.Tk{A.Bg{}, A.Queued{}}, A.mark(A.Ia{}, r), r, s, e, ad.f_mark_bi(r, Bool.or(s, A.hit(A.Waiting{}, A.Bg{}, A.Tk{A.Bg{}, A.Queued{}})), ad.f_tail(A.Bg{}, A.Tk{A.Bg{}, A.Queued{}}, r, s, e)))
        case _ A.Granted{}:
          ad.f_skip(A.Bg{}, A.Tk{hc, A.Granted{}}, A.mark(A.Ia{}, r), r, s, e, ad.f_mark_bi(r, Bool.or(s, A.hit(A.Waiting{}, A.Bg{}, A.Tk{hc, A.Granted{}})), ad.f_tail(A.Bg{}, A.Tk{hc, A.Granted{}}, r, s, e)))
        case _ A.Held{}:
          ad.f_skip(A.Bg{}, A.Tk{hc, A.Held{}}, A.mark(A.Ia{}, r), r, s, e, ad.f_mark_bi(r, Bool.or(s, A.hit(A.Waiting{}, A.Bg{}, A.Tk{hc, A.Held{}})), ad.f_tail(A.Bg{}, A.Tk{hc, A.Held{}}, r, s, e)))
        case _ A.Preempted{}:
          ad.f_skip(A.Bg{}, A.Tk{hc, A.Preempted{}}, A.mark(A.Ia{}, r), r, s, e, ad.f_mark_bi(r, Bool.or(s, A.hit(A.Waiting{}, A.Bg{}, A.Tk{hc, A.Preempted{}})), ad.f_tail(A.Bg{}, A.Tk{hc, A.Preempted{}}, r, s, e)))
        case _ A.Ended{}:
          ad.f_skip(A.Bg{}, A.Tk{hc, A.Ended{}}, A.mark(A.Ia{}, r), r, s, e, ad.f_mark_bi(r, Bool.or(s, A.hit(A.Waiting{}, A.Bg{}, A.Tk{hc, A.Ended{}})), ad.f_tail(A.Bg{}, A.Tk{hc, A.Ended{}}, r, s, e)))

def ad.f_grant(n: Nat, d: Maybe<&2, A.Cls>, +l: A.Lim, +t: List<&2, A.Tk>, +e: {A.fifo.both(t) == True{} : Bool}) -> {A.fifo.both(A.grant.go(n, d, l, t)) == True{} : Bool}:
  match n d:
    case 0n _:
      e
    case 1n+f None{}:
      e
    case 1n+f Some{A.Ia{}}:
      +t2 = A.mark(A.Ia{}, t)
      ad.f_grant(f, A.pick(l, t2), l, t2, ad.and_t(A.fifo(A.Ia{}, t2, False{}), A.fifo(A.Bg{}, t2, False{}), ad.f_mark(t, A.Ia{}, ad.and_l(A.fifo(A.Ia{}, t, False{}), A.fifo(A.Bg{}, t, False{}), e)), ad.f_mark_bi(t, False{}, ad.and_r(A.fifo(A.Ia{}, t, False{}), A.fifo(A.Bg{}, t, False{}), e))))
    case 1n+f Some{A.Bg{}}:
      +t2 = A.mark(A.Bg{}, t)
      ad.f_grant(f, A.pick(l, t2), l, t2, ad.and_t(A.fifo(A.Ia{}, t2, False{}), A.fifo(A.Bg{}, t2, False{}), ad.f_mark_ib(t, False{}, ad.and_l(A.fifo(A.Ia{}, t, False{}), A.fifo(A.Bg{}, t, False{}), e)), ad.f_mark(t, A.Bg{}, ad.and_r(A.fifo(A.Ia{}, t, False{}), A.fifo(A.Bg{}, t, False{}), e))))

def ad.f_end2(+ts: List<&2, A.Tk>, +k: Nat, +e: {A.fifo.both(ts) == True{} : Bool}) -> {A.fifo.both(A.put(ts, k, A.Ended{})) == True{} : Bool}:
  +t2 = A.put(ts, k, A.Ended{})
  ad.and_t(A.fifo(A.Ia{}, t2, False{}), A.fifo(A.Bg{}, t2, False{}), ad.f_end(ts, A.Ia{}, False{}, k, ad.and_l(A.fifo(A.Ia{}, ts, False{}), A.fifo(A.Bg{}, ts, False{}), e)), ad.f_end(ts, A.Bg{}, False{}, k, ad.and_r(A.fifo(A.Ia{}, ts, False{}), A.fifo(A.Bg{}, ts, False{}), e)))

def ad.f_end_grant(+l: A.Lim, +ts: List<&2, A.Tk>, +k: Nat, +e: {A.fifo.both(ts) == True{} : Bool}) -> {A.fifo.both(A.grant(l, A.put(ts, k, A.Ended{}))) == True{} : Bool}:
  +t2 = A.put(ts, k, A.Ended{})
  ad.f_grant(A.waits(t2), A.pick(l, t2), l, t2, ad.f_end2(ts, k, e))

def ad.isg_at(-ts: List<&2, A.Tk>, -k: Nat, -mb: Maybe<&2, A.Tk>, ej: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}, f: {ad.isg(mb) == True{} : Bool}) -> {ad.isg(A.get(ts, k)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, A.Tk>, A.get(ts, k), mb, ej) : {ad.isg(_) == True{} : Bool}
  f

def ad.f_col_op(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, ej: {A.get(ts, k) == mb : Maybe<&2, A.Tk>}, +e: {A.fifo.both(ts) == True{} : Bool}) -> {A.fifo.both(A.St.ts(A.collect.at(mb, l, q, ts, k))) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{A.Tk{c, A.Queued{}}}:
      e
    case Some{A.Tk{+c, A.Granted{}}}:
      +t2 = A.put(ts, k, A.Held{})
      +g = ad.isg_at(ts, k, Some{A.Tk{c, A.Granted{}}}, ej, {==})
      ad.and_t(A.fifo(A.Ia{}, t2, False{}), A.fifo(A.Bg{}, t2, False{}), ad.f_col(ts, A.Ia{}, False{}, k, ad.and_l(A.fifo(A.Ia{}, ts, False{}), A.fifo(A.Bg{}, ts, False{}), e), g), ad.f_col(ts, A.Bg{}, False{}, k, ad.and_r(A.fifo(A.Ia{}, ts, False{}), A.fifo(A.Bg{}, ts, False{}), e), g))
    case Some{A.Tk{c, A.Held{}}}:
      e
    case Some{A.Tk{c, A.Preempted{}}}:
      e
    case Some{A.Tk{c, A.Ended{}}}:
      e

def ad.f_rel_op(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, +e: {A.fifo.both(ts) == True{} : Bool}) -> {A.fifo.both(A.St.ts(A.release.at(mb, l, q, ts, k))) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{A.Tk{c, A.Queued{}}}:
      e
    case Some{A.Tk{c, A.Granted{}}}:
      e
    case Some{A.Tk{c, A.Held{}}}:
      ad.f_end_grant(l, ts, k, e)
    case Some{A.Tk{c, A.Preempted{}}}:
      ad.f_end2(ts, k, e)
    case Some{A.Tk{c, A.Ended{}}}:
      e

def ad.f_lea_op(mb: Maybe<&2, A.Tk>, +l: A.Lim, +q: Nat, +ts: List<&2, A.Tk>, +k: Nat, +e: {A.fifo.both(ts) == True{} : Bool}) -> {A.fifo.both(A.St.ts(A.leave.at(mb, l, q, ts, k))) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{A.Tk{c, A.Queued{}}}:
      ad.f_end_grant(l, ts, k, e)
    case Some{A.Tk{c, A.Granted{}}}:
      ad.f_end_grant(l, ts, k, e)
    case Some{A.Tk{c, A.Held{}}}:
      e
    case Some{A.Tk{c, A.Preempted{}}}:
      e
    case Some{A.Tk{c, A.Ended{}}}:
      e

def ad.fifo_ia_ok(wi: Nat, r: Bool, u: Bool) -> {Bool.or(Bool.not(Bool.and(A.Mode.of(A.Holding{}, A.admit.ia.st(Bool.and(A.isz(wi), r), u)), True{})), A.isz(wi)) == True{} : Bool}:
  match wi:
    case 0n:
      ad.or_t(Bool.not(Bool.and(A.Mode.of(A.Holding{}, A.admit.ia.st(r, u)), True{})))
    case 1n+w:
      match u:
        case True{}:
          {==}
        case False{}:
          {==}

def ad.fifo_bg_ok(a: Bool, b: Bool, w: Bool, r: Bool) -> {Bool.or(Bool.not(Bool.and(A.Mode.of(A.Holding{}, A.admit.bg.st(Bool.and(a, Bool.and(b, Bool.and(w, r))))), True{})), w) == True{} : Bool}:
  match a b w:
    case False{} _ _:
      {==}
    case True{} False{} _:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      ad.or_t(Bool.not(Bool.and(A.Mode.of(A.Holding{}, A.admit.bg.st(r)), True{})))

def ad.fifo_wi(-a: Nat, -b: Nat, -x: Bool, e: {b == a : Nat}, h: {Bool.or(x, A.isz(b)) == True{} : Bool}) -> {Bool.or(x, Bool.and(Bool.not(False{}), A.isz(a))) == True{} : Bool}:
  %e : {Bool.or(x, A.isz(_)) == True{} : Bool}
  h

def ad.f_step(s: A.St, o: A.Op, +e: {A.fifo.both(A.St.ts(s)) == True{} : Bool}) -> {A.fifo.both(A.St.ts(A.step(s, o))) == True{} : Bool}:
  match s o:
    case A.St{+l, +q, +ts} A.Admit{A.Ia{}}:
      +ei = ad.and_l(A.fifo(A.Ia{}, ts, False{}), A.fifo(A.Bg{}, ts, False{}), e)
      +hi = A.cnt(A.Holding{}, A.Ia{}, ts)
      +wi = A.cnt(A.Waiting{}, A.Ia{}, ts)
      +st = A.admit.ia.st(Bool.and(A.isz(wi), A.room(l, hi)), A.le(q, wi))
      +x = {A.Tk{A.Ia{}, st} : A.Tk}
      +t1 = A.preempt(ts)
      +t2 = List.append(&2, A.Tk, t1, [x])
      +oki = ad.fifo_wi(A.cnt(A.Waiting{}, A.Ia{}, t1), wi, Bool.not(A.hit(A.Holding{}, A.Ia{}, x)), Equal.sym(Nat, A.cnt(A.Waiting{}, A.Ia{}, t1), wi, ad.pre_ia(A.Waiting{}, ts)), ad.fifo_ia_ok(wi, A.room(l, hi), A.le(q, wi)))
      ad.and_t(A.fifo(A.Ia{}, t2, False{}), A.fifo(A.Bg{}, t2, False{}), ad.f_app(t1, A.Ia{}, False{}, x, Equal.trans(Bool, A.fifo(A.Ia{}, t1, False{}), A.fifo(A.Ia{}, ts, False{}), True{}, ad.f_pre_ia(ts, False{}), ei), oki), ad.f_app(t1, A.Bg{}, False{}, x, ad.f_pre_bg(ts, False{}), ad.or_nt(A.hit(A.Holding{}, A.Bg{}, x), Bool.and(True{}, A.isz(A.cnt(A.Waiting{}, A.Bg{}, t1))), ad.and_f(A.Mode.of(A.Holding{}, st)))))
    case A.St{+l, +q, +ts} A.Admit{A.Bg{}}:
      +ei = ad.and_l(A.fifo(A.Ia{}, ts, False{}), A.fifo(A.Bg{}, ts, False{}), e)
      +eb = ad.and_r(A.fifo(A.Ia{}, ts, False{}), A.fifo(A.Bg{}, ts, False{}), e)
      +hi = A.cnt(A.Holding{}, A.Ia{}, ts)
      +wi = A.cnt(A.Waiting{}, A.Ia{}, ts)
      +hb = A.cnt(A.Holding{}, A.Bg{}, ts)
      +wb = A.cnt(A.Waiting{}, A.Bg{}, ts)
      +st = A.admit.bg.st(Bool.and(A.isz(hi), Bool.and(A.isz(wi), Bool.and(A.isz(wb), A.room(l, Nat.add(hi, hb))))))
      +y = {A.Tk{A.Bg{}, st} : A.Tk}
      +t2 = List.append(&2, A.Tk, ts, [y])
      ad.and_t(A.fifo(A.Ia{}, t2, False{}), A.fifo(A.Bg{}, t2, False{}), ad.f_app(ts, A.Ia{}, False{}, y, ei, ad.or_nt(A.hit(A.Holding{}, A.Ia{}, y), Bool.and(True{}, A.isz(wi)), ad.and_f(A.Mode.of(A.Holding{}, st)))), ad.f_app(ts, A.Bg{}, False{}, y, eb, ad.fifo_bg_ok(A.isz(hi), A.isz(wi), A.isz(wb), A.room(l, Nat.add(hi, hb)))))
    case A.St{+l, +q, +ts} A.Collect{+k}:
      ad.f_col_op(A.get(ts, k), l, q, ts, k, {==}, e)
    case A.St{+l, +q, +ts} A.Release{+k}:
      ad.f_rel_op(A.get(ts, k), l, q, ts, k, e)
    case A.St{+l, +q, +ts} A.Leave{+k}:
      ad.f_lea_op(A.get(ts, k), l, q, ts, k, e)
    case A.St{+l, +q, +ts} A.Limit{+l2, q2}:
      ad.f_grant(A.waits(ts), A.pick(l2, ts), l2, ts, e)

def ad.run_fifo(os: List<&2, A.Op>, +s: A.St, e: {A.fifo.both(A.St.ts(s)) == True{} : Bool}) -> {A.fifo.both(A.St.ts(A.run(os, s))) == True{} : Bool}:
  match os:
    case Nil{}:
      e
    case +o <> r:
      ad.run_fifo(r, A.step(s, o), ad.f_step(s, o, e))

def fifo_per_class(+l: A.Lim, +q: Nat, +os: List<&2, A.Op>) -> {A.fifo.both(A.St.ts(A.run(os, A.St.new(l, q)))) == True{} : Bool}:
  ad.run_fifo(os, A.St.new(l, q), {==})

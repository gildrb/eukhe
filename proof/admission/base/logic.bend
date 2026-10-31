# eukhe: lemmas the proofs of area admission share: logic

import Base
import ../../../bend/admission.bend as Ad

# ---- admission ----

# proof_admission: the admission laws of LAWS.bend (rule H3 of
# LAWS.bend) over the model in admission.bend.

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

# what a count of mode m, class c sees of ticket mb
def ad.at(+m: Ad.Mode, +c: Ad.Cls, mb: Maybe<&2, Ad.Tk>) -> Bool:
  match mb:
    case None{}:
      False{}
    case Some{t}:
      Ad.hit(m, c, t)

def ad.absurd_t(-A: Type, e: {True{} == False{} : Bool}) -> A:
  ad.absurd(A, Equal.sym(Bool, True{}, False{}, e))

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

# a Some{c} that is not: refuted through its class
def ad.mis(m: Maybe<&2, Ad.Cls>, c: Ad.Cls) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{d}:
      Ad.Cls.eq(d, c)

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

# an interactive waiter: no slot is free
def ad.ok_room(r: Bool, -w: Nat, -hi: Nat, -wb: Nat, -c: Bool, h: {Bool.and(Bool.not(Maybe.is_some(&2, Ad.Cls, Ad.pick.go(r, 1n+w, hi, wb))), c) == True{} : Bool}) -> {r == False{} : Bool}:
  match r:
    case True{}:
      ad.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def ad.isg(m: Maybe<&2, Ad.Tk>) -> Bool:
  match m:
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      True{}
    case _:
      False{}

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

def ad.m_ia(-X: Type, -m: Maybe<&2, Ad.Cls>, e: {m == Some{Ad.Ia{}} : Maybe<&2, Ad.Cls>}, u: ad.BD(ad.mis(m, Ad.Ia{}), X, Unit)) -> X:
  %e : ad.BD(ad.mis(_, Ad.Ia{}), X, Unit)
  u

def ad.m_bg(-X: Type, -m: Maybe<&2, Ad.Cls>, e: {m == Some{Ad.Bg{}} : Maybe<&2, Ad.Cls>}, u: ad.BD(ad.mis(m, Ad.Bg{}), X, Unit)) -> X:
  %e : ad.BD(ad.mis(_, Ad.Bg{}), X, Unit)
  u

# ticket mb with status x
def ad.set(mb: Maybe<&2, Ad.Tk>, x: Ad.Sts) -> Maybe<&2, Ad.Tk>:
  match mb:
    case None{}:
      None{}
    case Some{Ad.Tk{c, s}}:
      Some{Ad.Tk{c, x}}

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

# eukhe: lemmas the proofs of area admission share: bool

import Base
import ../../../bend/admission.bend as Ad

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

# what a count of mode m, class c sees of ticket mb
def ad.at(+m: Ad.Mode, +c: Ad.Cls, mb: Maybe<&2, Ad.Tk>) -> Bool:
  match mb:
    case None{}:
      False{}
    case Some{t}:
      Ad.hit(m, c, t)

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

def ad.not_none(-m: Maybe<&2, Ad.Cls>, e: {m == None{} : Maybe<&2, Ad.Cls>}) -> {Bool.not(Maybe.is_some(&2, Ad.Cls, m)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Ad.Cls>, m, None{}, e) : {Bool.not(Maybe.is_some(&2, Ad.Cls, _)) == True{} : Bool}
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

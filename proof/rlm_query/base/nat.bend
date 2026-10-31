# eukhe: Nat lemmas of the proofs of area rlm_query: sums (rq.add_*),
# the order (rq.le_*) and the room left under a bound (rq.sub_*)

import Base

# Logic
# -----

def rq.BF(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      A

# True is not False
def rq.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : rq.BF(_, A)
  Unit{}

# Sums
# ----

def rq.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, rq.add_zero(p))

def rq.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), rq.add_succ(p, b))

def rq.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), rq.add_assoc(p, b, c))

# Order
# -----

def rq.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def rq.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      rq.le_refl(p)

def rq.le_step(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      rq.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      rq.le_step(p, q, h)

def rq.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      rq.le_zero(c)
    case 1n+p 0n _:
      rq.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, ab))
    case 1n+p 1n+q 0n:
      rq.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, bc))
    case 1n+p 1n+q 1n+s:
      rq.le_trans(p, q, s, ab, bc)

# r is at most m + r
def rq.le_add(m: Nat, +r: Nat) -> {Nat.is_le(r, Nat.add(m, r)) == True{} : Bool}:
  match m:
    case 0n:
      rq.le_refl(r)
    case 1n++p:
      rq.le_step(r, Nat.add(p, r), rq.le_add(p, r))

def rq.lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      rq.absurd({Nat.is_le(a, 0n) == True{} : Bool}, Equal.sym(Bool, Nat.is_lt(a, 0n), True{}, Equal.trans(Bool, Nat.is_lt(a, 0n), True{}, True{}, h, {==})))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      rq.lt_le(p, q, h)

# a below b: b is not at most a
def rq.lt_not_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      rq.absurd({Nat.is_le(0n, a) == False{} : Bool}, Equal.sym(Bool, Nat.is_lt(a, 0n), True{}, Equal.trans(Bool, Nat.is_lt(a, 0n), True{}, True{}, h, {==})))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      rq.lt_not_le(p, q, h)

# a at most b: b is not below a
def rq.le_not_lt(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n _:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p 0n:
      rq.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      rq.le_not_lt(p, q, h)

def rq.min_le_l(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rq.min_le_l(p, q)

# c not at most r: r is below c
def rq.nle_lt(c: Nat, r: Nat, h: {Nat.is_le(c, r) == False{} : Bool}) -> {Nat.is_lt(r, c) == True{} : Bool}:
  match c r:
    case 0n _:
      rq.absurd({Nat.is_lt(r, 0n) == True{} : Bool}, Equal.trans(Bool, True{}, Nat.is_le(0n, r), False{}, Equal.sym(Bool, Nat.is_le(0n, r), True{}, rq.le_zero(r)), h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rq.nle_lt(p, q, h)

def rq.min_le_r(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      rq.le_zero(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rq.min_le_r(p, q)

# Room
# ----

def rq.sub_zero(m: Nat) -> {Nat.sub(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

# r below c leaves room
def rq.sub_pos(r: Nat, c: Nat, h: {Nat.is_lt(r, c) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.sub(c, r)) == True{} : Bool}:
  match r c:
    case _ 0n:
      rq.absurd({Nat.is_lt(0n, Nat.sub(0n, r)) == True{} : Bool}, Equal.sym(Bool, Nat.is_lt(r, 0n), True{}, Equal.trans(Bool, Nat.is_lt(r, 0n), True{}, True{}, h, {==})))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      rq.sub_pos(p, q, h)

# x within the room c - r of r below c: r + x is within c
def rq.sub_add_le(r: Nat, c: Nat, +x: Nat, hx: {Nat.is_le(x, Nat.sub(c, r)) == True{} : Bool}, hr: {Nat.is_le(r, c) == True{} : Bool}) -> {Nat.is_le(Nat.add(r, x), c) == True{} : Bool}:
  match r c:
    case 0n 0n:
      hx
    case 0n 1n+q:
      hx
    case 1n+p 0n:
      rq.absurd({Nat.is_le(Nat.add(1n+p, x), 0n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, hr))
    case 1n+p 1n+q:
      rq.sub_add_le(p, q, x, hx, hr)

# within m, w + u is within m exactly when u is within m - w
def rq.le_shift(w: Nat, m: Nat, +u: Nat, h: {Nat.is_le(w, m) == True{} : Bool}) -> {Nat.is_le(Nat.add(w, u), m) == Nat.is_le(u, Nat.sub(m, w)) : Bool}:
  match w m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      rq.absurd({Nat.is_le(Nat.add(1n+p, u), 0n) == Nat.is_le(u, Nat.sub(0n, 1n+p)) : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      rq.le_shift(p, q, u, h)

# past m, w + u is past m
def rq.le_past(w: Nat, m: Nat, -u: Nat, h: {Nat.is_le(w, m) == False{} : Bool}) -> {Nat.is_le(Nat.add(w, u), m) == False{} : Bool}:
  match w m:
    case 0n _:
      rq.absurd({Nat.is_le(Nat.add(0n, u), m) == False{} : Bool}, Equal.trans(Bool, True{}, Nat.is_le(0n, m), False{}, Equal.sym(Bool, Nat.is_le(0n, m), True{}, rq.le_zero(m)), h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rq.le_past(p, q, u, h)

# taking w then u is taking w + u
def rq.sub_sub(m: Nat, w: Nat, +u: Nat) -> {Nat.sub(m, Nat.add(w, u)) == Nat.sub(Nat.sub(m, w), u) : Nat}:
  match m w:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rq.sub_sub(p, q, u)

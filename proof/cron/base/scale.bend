# eukhe: lemmas the proofs of area cron share: a clock of unit u = 1 + v
# (the store's ms on the model's minutes). Scaling keeps sums and order:
# (a + b) * u = a * u + b * u, and a * u compares to b * u as a to b.
# Each lemma reads simple == scaled, so a rewrite turns the scaled form
# the spec computes into the form the model's step scales.

import Base

# a + (b + c) = (a + b) + c
def crsc.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %crsc.add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# (a + b) * u = a * u + b * u
def crsc.dist(a: Nat, -b: Nat, +u: Nat) -> {Nat.mul(Nat.add(a, b), u) == Nat.add(Nat.mul(a, u), Nat.mul(b, u)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %crsc.add_assoc(u, Nat.mul(p, u), Nat.mul(b, u)) : {Nat.add(u, Nat.mul(Nat.add(p, b), u)) == _ : Nat}
      %crsc.dist(p, b, u) : {Nat.add(u, Nat.mul(Nat.add(p, b), u)) == Nat.add(u, _) : Nat}
      {==}

# w + x compares to w + y as x to y
def crsc.cmp_add(w: Nat, -x: Nat, -y: Nat) -> {Nat.cmp(x, y) == Nat.cmp(Nat.add(w, x), Nat.add(w, y)) : Cmp}:
  match w:
    case 0n:
      {==}
    case 1n+q:
      crsc.cmp_add(q, x, y)

# a * u compares to b * u as a to b, for u = 1 + v
def crsc.cmp_mul(a: Nat, b: Nat, +v: Nat) -> {Nat.cmp(a, b) == Nat.cmp(Nat.mul(a, 1n+v), Nat.mul(b, 1n+v)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %crsc.cmp_add(1n+v, Nat.mul(p, 1n+v), Nat.mul(q, 1n+v)) : {Nat.cmp(p, q) == _ : Cmp}
      crsc.cmp_mul(p, q, v)

def crsc.le_mul(+a: Nat, +b: Nat, +v: Nat) -> {Nat.is_le(a, b) == Nat.is_le(Nat.mul(a, 1n+v), Nat.mul(b, 1n+v)) : Bool}:
  %crsc.cmp_mul(a, b, v) : {Nat.is_le(a, b) == Cmp.is_le(_) : Bool}
  {==}

def crsc.lt_mul(+a: Nat, +b: Nat, +v: Nat) -> {Nat.is_lt(a, b) == Nat.is_lt(Nat.mul(a, 1n+v), Nat.mul(b, 1n+v)) : Bool}:
  %crsc.cmp_mul(a, b, v) : {Nat.is_lt(a, b) == Cmp.is_lt(_) : Bool}
  {==}

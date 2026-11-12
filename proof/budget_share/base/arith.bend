# eukhe: arithmetic lemmas of the proofs of area budget_share: Base's
# Nat.div (Nat.divmod.go) against Nat.mul, so a share within what is free
# divided by n, n times, is within what is free (bsa.mul_div_le,
# bsa.leaves), and a share of one agent is all of it (bsa.div_one)

import Base
import ../../budget/base/reserve.bend as BR

# Sums
# ----

# a + (b + c) = b + (a + c)
def bsa.add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)), Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), BR.br.add_assoc(a, b, c)), Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)), Equal.cong(Nat, Nat, z => Nat.add(z, c), Nat.add(a, b), Nat.add(b, a), BR.br.add_comm(a, b)), BR.br.add_assoc(b, a, c)))

# (a + b) + (c + d) = (a + c) + (b + d)
def bsa.add_swap4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), BR.br.add_assoc(a, b, Nat.add(c, d)), Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), bsa.add_swap(b, c, d)), Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), BR.br.add_assoc(a, c, Nat.add(b, d)))))

# Products
# --------

# k * 0 = 0
def bsa.mul_zero(k: Nat) -> {Nat.mul(k, 0n) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      bsa.mul_zero(p)

# k * (1 + d) = k + k * d
def bsa.mul_succ_r(k: Nat, +d: Nat) -> {Nat.mul(k, 1n+d) == Nat.add(k, Nat.mul(k, d)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(d, Nat.mul(p, 1n+d)), Nat.add(p, Nat.add(d, Nat.mul(p, d))), Equal.trans(Nat, Nat.add(d, Nat.mul(p, 1n+d)), Nat.add(d, Nat.add(p, Nat.mul(p, d))), Nat.add(p, Nat.add(d, Nat.mul(p, d))), Equal.cong(Nat, Nat, z => Nat.add(d, z), Nat.mul(p, 1n+d), Nat.add(p, Nat.mul(p, d)), bsa.mul_succ_r(p, d)), bsa.add_swap(d, p, Nat.mul(p, d))))

# m * (y + x) = m * y + m * x
def bsa.mul_add_r(m: Nat, +y: Nat, +x: Nat) -> {Nat.mul(m, Nat.add(y, x)) == Nat.add(Nat.mul(m, y), Nat.mul(m, x)) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat, Nat.add(Nat.add(y, x), Nat.mul(p, Nat.add(y, x))), Nat.add(Nat.add(y, x), Nat.add(Nat.mul(p, y), Nat.mul(p, x))), Nat.add(Nat.add(y, Nat.mul(p, y)), Nat.add(x, Nat.mul(p, x))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(y, x), z), Nat.mul(p, Nat.add(y, x)), Nat.add(Nat.mul(p, y), Nat.mul(p, x)), bsa.mul_add_r(p, y, x)), bsa.add_swap4(y, x, Nat.mul(p, y), Nat.mul(p, x)))

# x <= q: k * x <= k * q
def bsa.mul_mono_r(k: Nat, +x: Nat, +q: Nat, h: {Nat.is_le(x, q) == True{} : Bool}) -> {Nat.is_le(Nat.mul(k, x), Nat.mul(k, q)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      +h0 = h
      BR.br.le_trans(Nat.add(x, Nat.mul(p, x)), Nat.add(q, Nat.mul(p, x)), Nat.add(q, Nat.mul(p, q)), BR.br.mono_l(x, q, Nat.mul(p, x), h0), BR.br.mono_r(q, Nat.mul(p, x), Nat.mul(p, q), bsa.mul_mono_r(p, x, q, h0)))

# Division
# --------

# dividing by 1 counts every unit: the quotient of divmod.go with no
# divisor left is n + d
def bsa.go_one(n: Nat, +d: Nat) -> {Pair.fst(Nat, Nat, Nat.divmod.go(n, 0n, d, 0n)) == Nat.add(n, d) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(p, 0n, 1n+d, 0n)), Nat.add(p, 1n+d), 1n+Nat.add(p, d), bsa.go_one(p, 1n+d), BR.br.add_succ(p, d))

# r / 1 = r
def bsa.div_one(+r: Nat) -> {Nat.div(r, 1n) == r : Nat}:
  Equal.trans(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(r, 0n, 0n, 0n)), Nat.add(r, 0n), r, bsa.go_one(r, 0n), BR.br.add_zero(r))

# the quotient divmod.go(n, mm, d, r) reaches, k + 1 times, is at most n
# with d, k + 1 times, and r, while mm + r is k (mm: what is left of the
# divisor less one, r: what was counted of it)
def bsa.go_le(n: Nat, mm: Nat, +d: Nat, +r: Nat, +k: Nat, h: {Nat.add(mm, r) == k : Nat}) -> {Nat.is_le(Nat.mul(1n+k, Pair.fst(Nat, Nat, Nat.divmod.go(n, mm, d, r))), Nat.add(n, Nat.add(Nat.mul(1n+k, d), r))) == True{} : Bool}:
  match n mm:
    case 0n x:
      BR.br.le_self(Nat.mul(1n+k, d), r)
    case 1n++np 0n:
      +h0 = h
      +x = Nat.mul(1n+k, d)
      +q = Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))
      +s1 = Equal.trans(Nat, Nat.add(Nat.mul(1n+k, 1n+d), 0n), Nat.mul(1n+k, 1n+d), Nat.add(1n+k, x), BR.br.add_zero(Nat.mul(1n+k, 1n+d)), bsa.mul_succ_r(1n+k, d))
      +s3 = Equal.cong(Nat, Nat, z => Nat.add(np, z), Nat.add(Nat.mul(1n+k, 1n+d), 0n), 1n+Nat.add(k, x), s1)
      +s5 = Equal.trans(Nat, Nat.add(k, x), Nat.add(x, k), Nat.add(x, r), BR.br.add_comm(k, x), Equal.cong(Nat, Nat, z => Nat.add(x, z), k, r, Equal.sym(Nat, r, k, h0)))
      +s6 = Equal.cong(Nat, Nat, z => 1n+Nat.add(np, z), Nat.add(k, x), Nat.add(x, r), s5)
      +eq = Equal.trans(Nat, Nat.add(np, Nat.add(Nat.mul(1n+k, 1n+d), 0n)), Nat.add(np, 1n+Nat.add(k, x)), 1n+Nat.add(np, Nat.add(x, r)), s3, Equal.trans(Nat, Nat.add(np, 1n+Nat.add(k, x)), 1n+Nat.add(np, Nat.add(k, x)), 1n+Nat.add(np, Nat.add(x, r)), BR.br.add_succ(np, Nat.add(k, x)), s6))
      %eq : {Nat.is_le(Nat.mul(1n+k, q), _) == True{} : Bool}
      bsa.go_le(np, r, 1n+d, 0n, k, Equal.trans(Nat, Nat.add(r, 0n), r, k, BR.br.add_zero(r), h0))
    case 1n++np 1n++mp:
      +x = Nat.mul(1n+k, d)
      +q = Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r))
      +eq = Equal.trans(Nat, Nat.add(np, Nat.add(x, 1n+r)), Nat.add(np, 1n+Nat.add(x, r)), 1n+Nat.add(np, Nat.add(x, r)), Equal.cong(Nat, Nat, z => Nat.add(np, z), Nat.add(x, 1n+r), 1n+Nat.add(x, r), BR.br.add_succ(x, r)), BR.br.add_succ(np, Nat.add(x, r)))
      %eq : {Nat.is_le(Nat.mul(1n+k, q), _) == True{} : Bool}
      bsa.go_le(np, mp, d, 1n+r, k, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), k, BR.br.add_succ(mp, r), h))

# (m + 1) * (r / (m + 1)) <= r
def bsa.mul_div_le(+r: Nat, +m: Nat) -> {Nat.is_le(Nat.mul(1n+m, Nat.div(r, 1n+m)), r) == True{} : Bool}:
  +e1 = Equal.trans(Nat, Nat.add(Nat.mul(1n+m, 0n), 0n), Nat.mul(1n+m, 0n), 0n, BR.br.add_zero(Nat.mul(1n+m, 0n)), bsa.mul_zero(m))
  +e2 = Equal.trans(Nat, Nat.add(r, Nat.add(Nat.mul(1n+m, 0n), 0n)), Nat.add(r, 0n), r, Equal.cong(Nat, Nat, z => Nat.add(r, z), Nat.add(Nat.mul(1n+m, 0n), 0n), 0n, e1), BR.br.add_zero(r))
  %e2 : {Nat.is_le(Nat.mul(1n+m, Pair.fst(Nat, Nat, Nat.divmod.go(r, m, 0n, 0n))), _) == True{} : Bool}
  bsa.go_le(r, m, 0n, 0n, m, BR.br.add_zero(m))

# a share x within r / (m + 1) leaves, m + 1 times, what is left of r past
# it at least m times r
def bsa.leaves(+m: Nat, +r: Nat, +x: Nat, h: {Nat.is_le(x, Nat.div(r, 1n+m)) == True{} : Bool}) -> {Nat.is_le(Nat.mul(m, r), Nat.mul(1n+m, Nat.sub(r, x))) == True{} : Bool}:
  +e1 = BR.br.le_trans(Nat.mul(1n+m, x), Nat.mul(1n+m, Nat.div(r, 1n+m)), r, bsa.mul_mono_r(1n+m, x, Nat.div(r, 1n+m), h), bsa.mul_div_le(r, m))
  +y = Nat.sub(r, x)
  +e2 = BR.br.le_sub(x, r, Nat.mul(m, x), e1)
  +e3 = BR.br.take(x, Nat.mul(m, x), r, e1)
  %e3 : {Nat.is_le(Nat.mul(m, _), Nat.mul(1n+m, y)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(m, Nat.add(y, x)), Nat.add(Nat.mul(m, y), Nat.mul(m, x)), bsa.mul_add_r(m, y, x)) : {Nat.is_le(_, Nat.mul(1n+m, y)) == True{} : Bool}
  %BR.br.add_comm(Nat.mul(m, y), y) : {Nat.is_le(Nat.add(Nat.mul(m, y), Nat.mul(m, x)), _) == True{} : Bool}
  BR.br.mono_r(Nat.mul(m, y), Nat.mul(m, x), y, e2)

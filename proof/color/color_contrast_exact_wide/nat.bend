# eukhe: the Nat lemmas of LAW color_contrast_exact_wide: division with
# remainder by a base 1 + k (Nat.divmod.go keeps quotient·(1 + k) +
# remainder + what is left of n, the remainder below 1 + k), the product
# laws, and the comparison of two numbers split at the base: the high
# parts first, the remainders on a tie. The base stays abstract here; the
# fill instantiates it once at 2^16.

import Base
import ../../base/nat.bend as LNat

# Truth
# -----

def cw.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def cw.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : cw.If(_, G)
  Unit{}

# Products
# --------

# (a + b)·c = a·c + b·c
def cw.mul_add_r(a: Nat, -b: Nat, +c: Nat) -> {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), cw.mul_add_r(p, b, c)) : {Nat.add(c, _) == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) : Nat}
      LNat.add_assoc_r(c, Nat.mul(p, c), Nat.mul(b, c))

# (a·b)·c = a·(b·c)
def cw.mul_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(Nat.add(b, Nat.mul(p, b)), c), Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)), cw.mul_add_r(b, Nat.mul(p, b), c)) : {_ == Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) : Nat}
      %cw.mul_assoc(p, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

# (a + b) + (c + d) = (a + c) + (b + d)
def cw.add4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)),
    LNat.add_assoc(a, b, Nat.add(c, d)),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)),
      Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), LNat.add_lcomm(b, c, d)),
      LNat.add_assoc_r(a, c, Nat.add(b, d))))

# x·(a + b) = x·a + x·b
def cw.mul_add_l(x: Nat, +a: Nat, +b: Nat) -> {Nat.mul(x, Nat.add(a, b)) == Nat.add(Nat.mul(x, a), Nat.mul(x, b)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(p, Nat.add(a, b)), Nat.add(Nat.mul(p, a), Nat.mul(p, b)), cw.mul_add_l(p, a, b)) : {Nat.add(Nat.add(a, b), _) == Nat.add(Nat.add(a, Nat.mul(p, a)), Nat.add(b, Nat.mul(p, b))) : Nat}
      cw.add4(a, b, Nat.mul(p, a), Nat.mul(p, b))

# Division with remainder
# -----------------------

# the carry step: n + ((1 + k + M) + 0) = 1 + n + (M + k)
def cw.carry(+n: Nat, +k: Nat, +M: Nat) -> {Nat.add(n, Nat.add(Nat.add(1n+k, M), 0n)) == 1n+Nat.add(n, Nat.add(M, k)) : Nat}:
  Equal.trans(Nat, Nat.add(n, 1n+Nat.add(Nat.add(k, M), 0n)), 1n+Nat.add(n, Nat.add(Nat.add(k, M), 0n)), 1n+Nat.add(n, Nat.add(M, k)),
    LNat.add_succ(n, Nat.add(Nat.add(k, M), 0n)),
    Equal.trans(Nat, 1n+Nat.add(n, Nat.add(Nat.add(k, M), 0n)), 1n+Nat.add(n, Nat.add(k, M)), 1n+Nat.add(n, Nat.add(M, k)),
      Equal.cong(Nat, Nat, z => 1n+Nat.add(n, z), Nat.add(Nat.add(k, M), 0n), Nat.add(k, M), LNat.add_zero(Nat.add(k, M))),
      Equal.cong(Nat, Nat, z => 1n+Nat.add(n, z), Nat.add(k, M), Nat.add(M, k), LNat.add_comm(k, M))))

# the count step: n + (M + (1 + r)) = 1 + n + (M + r)
def cw.count(+n: Nat, +M: Nat, +r: Nat) -> {Nat.add(n, Nat.add(M, 1n+r)) == 1n+Nat.add(n, Nat.add(M, r)) : Nat}:
  Equal.trans(Nat, Nat.add(n, Nat.add(M, 1n+r)), Nat.add(n, 1n+Nat.add(M, r)), 1n+Nat.add(n, Nat.add(M, r)),
    Equal.cong(Nat, Nat, z => Nat.add(n, z), Nat.add(M, 1n+r), 1n+Nat.add(M, r), LNat.add_succ(M, r)),
    LNat.add_succ(n, Nat.add(M, r)))

# Nat.divmod.go from n, m left before the next carry, quotient d and
# remainder r so far (m + r = k): quotient·(1 + k) + remainder is
# n + d·(1 + k) + r
def cw.go_eq(n: Nat, m: Nat, +d: Nat, +r: Nat, +k: Nat, +h: {Nat.add(m, r) == k : Nat}) -> {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+k), Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r))) == Nat.add(n, Nat.add(Nat.mul(d, 1n+k), r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++np:
      match m:
        case 0n:
          Equal.trans(Nat, Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), 1n+k), Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))), Nat.add(np, Nat.add(Nat.mul(1n+d, 1n+k), 0n)), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+k), r)),
            cw.go_eq(np, r, 1n+d, 0n, k, Equal.trans(Nat, Nat.add(r, 0n), r, k, LNat.add_zero(r), h)),
            Equal.trans(Nat, Nat.add(np, Nat.add(Nat.mul(1n+d, 1n+k), 0n)), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+k), k)), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+k), r)),
              cw.carry(np, k, Nat.mul(d, 1n+k)),
              Equal.cong(Nat, Nat, z => 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+k), z)), k, r, Equal.sym(Nat, r, k, h))))
        case 1n++mp:
          Equal.trans(Nat, Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)), 1n+k), Pair.snd(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r))), Nat.add(np, Nat.add(Nat.mul(d, 1n+k), 1n+r)), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+k), r)),
            cw.go_eq(np, mp, d, 1n+r, k, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), k, LNat.add_succ(mp, r), h)),
            cw.count(np, Nat.mul(d, 1n+k), r))

# a is below 1 + b when a is at most b
def cw.lt_of_le(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      cw.absurd({Nat.is_lt(1n+p, 1n+0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      cw.lt_of_le(p, q, h)

# the remainder of Nat.divmod.go stays below 1 + k (m + r = k)
def cw.go_lt(n: Nat, +m: Nat, +d: Nat, +r: Nat, +k: Nat, h: {Nat.add(m, r) == k : Nat}) -> {Nat.is_lt(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+k) == True{} : Bool}:
  match n:
    case 0n:
      %h : {Nat.is_lt(r, 1n+_) == True{} : Bool}
      cw.lt_of_le(r, Nat.add(m, r), LNat.compactor.pc.le_add(m, r))
    case 1n+np:
      match m:
        case 0n:
          cw.go_lt(np, r, 1n+d, 0n, k, Equal.trans(Nat, Nat.add(r, 0n), r, k, LNat.add_zero(r), h))
        case 1n++mp:
          cw.go_lt(np, mp, d, 1n+r, k, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), k, LNat.add_succ(mp, r), h))

# x div (1 + k) · (1 + k) + x mod (1 + k) = x
def cw.dm_eq(+x: Nat, +k: Nat) -> {Nat.add(Nat.mul(Nat.div(x, 1n+k), 1n+k), Nat.mod(x, 1n+k)) == x : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(x, 1n+k), 1n+k), Nat.mod(x, 1n+k)), Nat.add(x, 0n), x,
    cw.go_eq(x, k, 0n, 0n, k, LNat.add_zero(k)),
    LNat.add_zero(x))

# x mod (1 + k) is below 1 + k
def cw.dm_lt(+x: Nat, +k: Nat) -> {Nat.is_lt(Nat.mod(x, 1n+k), 1n+k) == True{} : Bool}:
  cw.go_lt(x, k, 0n, 0n, k, LNat.add_zero(k))

# Splitting a product at the base
# -------------------------------

# the high part of x·n at base 1 + k: x·(n div (1 + k)) plus the carry of
# x·(n mod (1 + k))
def cw.hi(+x: Nat, +n: Nat, +k: Nat) -> Nat:
  Nat.add(Nat.mul(x, Nat.div(n, 1n+k)), Nat.div(Nat.mul(x, Nat.mod(n, 1n+k)), 1n+k))

# the low part of x·n at base 1 + k
def cw.lo(+x: Nat, +n: Nat, +k: Nat) -> Nat:
  Nat.mod(Nat.mul(x, Nat.mod(n, 1n+k)), 1n+k)

# with n = q·(1 + k) + r and x·r = q2·(1 + k) + r2:
# (x·q + q2)·(1 + k) + r2 = x·n
def cw.recombine(+x: Nat, +n: Nat, +q: Nat, +r: Nat, +q2: Nat, +r2: Nat, +k: Nat, e1: {Nat.add(Nat.mul(q, 1n+k), r) == n : Nat}, e2: {Nat.add(Nat.mul(q2, 1n+k), r2) == Nat.mul(x, r) : Nat}) -> {Nat.add(Nat.mul(Nat.add(Nat.mul(x, q), q2), 1n+k), r2) == Nat.mul(x, n) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(Nat.mul(x, q), q2), 1n+k), r2), Nat.add(Nat.add(Nat.mul(Nat.mul(x, q), 1n+k), Nat.mul(q2, 1n+k)), r2), Nat.mul(x, n),
    Equal.cong(Nat, Nat, z => Nat.add(z, r2), Nat.mul(Nat.add(Nat.mul(x, q), q2), 1n+k), Nat.add(Nat.mul(Nat.mul(x, q), 1n+k), Nat.mul(q2, 1n+k)), cw.mul_add_r(Nat.mul(x, q), q2, 1n+k)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(x, q), 1n+k), Nat.mul(q2, 1n+k)), r2), Nat.add(Nat.mul(Nat.mul(x, q), 1n+k), Nat.add(Nat.mul(q2, 1n+k), r2)), Nat.mul(x, n),
      LNat.add_assoc(Nat.mul(Nat.mul(x, q), 1n+k), Nat.mul(q2, 1n+k), r2),
      Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(x, q), 1n+k), Nat.add(Nat.mul(q2, 1n+k), r2)), Nat.add(Nat.mul(Nat.mul(x, q), 1n+k), Nat.mul(x, r)), Nat.mul(x, n),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(Nat.mul(x, q), 1n+k), z), Nat.add(Nat.mul(q2, 1n+k), r2), Nat.mul(x, r), e2),
        Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(x, q), 1n+k), Nat.mul(x, r)), Nat.add(Nat.mul(x, Nat.mul(q, 1n+k)), Nat.mul(x, r)), Nat.mul(x, n),
          Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(x, r)), Nat.mul(Nat.mul(x, q), 1n+k), Nat.mul(x, Nat.mul(q, 1n+k)), cw.mul_assoc(x, q, 1n+k)),
          Equal.trans(Nat, Nat.add(Nat.mul(x, Nat.mul(q, 1n+k)), Nat.mul(x, r)), Nat.mul(x, Nat.add(Nat.mul(q, 1n+k), r)), Nat.mul(x, n),
            Equal.sym(Nat, Nat.mul(x, Nat.add(Nat.mul(q, 1n+k), r)), Nat.add(Nat.mul(x, Nat.mul(q, 1n+k)), Nat.mul(x, r)), cw.mul_add_l(x, Nat.mul(q, 1n+k), r)),
            Equal.cong(Nat, Nat, z => Nat.mul(x, z), Nat.add(Nat.mul(q, 1n+k), r), n, e1))))))

# hi·(1 + k) + lo = x·n
def cw.split_eq(+x: Nat, +n: Nat, +k: Nat) -> {Nat.add(Nat.mul(cw.hi(x, n, k), 1n+k), cw.lo(x, n, k)) == Nat.mul(x, n) : Nat}:
  cw.recombine(x, n, Nat.div(n, 1n+k), Nat.mod(n, 1n+k), Nat.div(Nat.mul(x, Nat.mod(n, 1n+k)), 1n+k), Nat.mod(Nat.mul(x, Nat.mod(n, 1n+k)), 1n+k), k, cw.dm_eq(n, k), cw.dm_eq(Nat.mul(x, Nat.mod(n, 1n+k)), k))

# Comparing split numbers
# -----------------------

# the comparison of a·(1 + k) + b with c·(1 + k) + d, b and d below the
# base: a below c, or a equal to c and b at most d
def cw.lexle(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> Bool:
  Bool.or(Nat.is_lt(a, c), Bool.and(Nat.is_eq(a, c), Nat.is_le(b, d)))

# b below 1 + k is at most 1 + (k + X) + d
def cw.lex_lo(b: Nat, k: Nat, +X: Nat, +d: Nat, hb: {Nat.is_lt(b, 1n+k) == True{} : Bool}) -> {Nat.is_le(b, 1n+Nat.add(Nat.add(k, X), d)) == True{} : Bool}:
  match b k:
    case 0n _:
      {==}
    case 1n+bp 0n:
      cw.absurd({Nat.is_le(1n+bp, 1n+Nat.add(Nat.add(0n, X), d)) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(bp, 0n), True{}, LNat.pu.lt_zero_f(bp), hb))
    case 1n+bp 1n+kp:
      cw.lex_lo(bp, kp, X, d, hb)

# 1 + (k + X) + b is not at most d below 1 + k
def cw.lex_hi(d: Nat, k: Nat, +X: Nat, +b: Nat, hd: {Nat.is_lt(d, 1n+k) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(Nat.add(k, X), b), d) == False{} : Bool}:
  match d k:
    case 0n _:
      {==}
    case 1n+dp 0n:
      cw.absurd({Nat.is_le(1n+Nat.add(Nat.add(0n, X), b), 1n+dp) == False{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(dp, 0n), True{}, LNat.pu.lt_zero_f(dp), hd))
    case 1n+dp 1n+kp:
      cw.lex_hi(dp, kp, X, b, hd)

# a common k cancels: (k + X) + b <= (k + Y) + d is X + b <= Y + d
def cw.cancel(k: Nat, +X: Nat, +b: Nat, +Y: Nat, +d: Nat) -> {Nat.is_le(Nat.add(Nat.add(k, X), b), Nat.add(Nat.add(k, Y), d)) == Nat.is_le(Nat.add(X, b), Nat.add(Y, d)) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+kp:
      cw.cancel(kp, X, b, Y, d)

# a·(1 + k) + b <= c·(1 + k) + d, b and d below 1 + k, is the comparison
# of the high parts first, the low parts on a tie
def cw.lex(a: Nat, c: Nat, +b: Nat, +d: Nat, +k: Nat, hb: {Nat.is_lt(b, 1n+k) == True{} : Bool}, hd: {Nat.is_lt(d, 1n+k) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.mul(a, 1n+k), b), Nat.add(Nat.mul(c, 1n+k), d)) == cw.lexle(a, b, c, d) : Bool}:
  match a c:
    case 0n 0n:
      {==}
    case 0n 1n+cp:
      cw.lex_lo(b, k, Nat.mul(cp, 1n+k), d, hb)
    case 1n+ap 0n:
      cw.lex_hi(d, k, Nat.mul(ap, 1n+k), b, hd)
    case 1n++ap 1n++cp:
      Equal.trans(Bool, Nat.is_le(Nat.add(Nat.add(k, Nat.mul(ap, 1n+k)), b), Nat.add(Nat.add(k, Nat.mul(cp, 1n+k)), d)), Nat.is_le(Nat.add(Nat.mul(ap, 1n+k), b), Nat.add(Nat.mul(cp, 1n+k), d)), cw.lexle(ap, b, cp, d),
        cw.cancel(k, Nat.mul(ap, 1n+k), b, Nat.mul(cp, 1n+k), d),
        cw.lex(ap, cp, b, d, k, hb, hd))

# d·n <= l·e is the comparison of their parts split at the base 1 + k
def cw.split_le(+d: Nat, +n: Nat, +l: Nat, +e: Nat, +k: Nat) -> {cw.lexle(cw.hi(d, n, k), cw.lo(d, n, k), cw.hi(l, e, k), cw.lo(l, e, k)) == Nat.is_le(Nat.mul(d, n), Nat.mul(l, e)) : Bool}:
  %cw.split_eq(d, n, k) : {cw.lexle(cw.hi(d, n, k), cw.lo(d, n, k), cw.hi(l, e, k), cw.lo(l, e, k)) == Nat.is_le(_, Nat.mul(l, e)) : Bool}
  %cw.split_eq(l, e, k) : {cw.lexle(cw.hi(d, n, k), cw.lo(d, n, k), cw.hi(l, e, k), cw.lo(l, e, k)) == Nat.is_le(Nat.add(Nat.mul(cw.hi(d, n, k), 1n+k), cw.lo(d, n, k)), _) : Bool}
  Equal.sym(Bool, Nat.is_le(Nat.add(Nat.mul(cw.hi(d, n, k), 1n+k), cw.lo(d, n, k)), Nat.add(Nat.mul(cw.hi(l, e, k), 1n+k), cw.lo(l, e, k))), cw.lexle(cw.hi(d, n, k), cw.lo(d, n, k), cw.hi(l, e, k), cw.lo(l, e, k)),
    cw.lex(cw.hi(d, n, k), cw.hi(l, e, k), cw.lo(d, n, k), cw.lo(l, e, k), k, cw.dm_lt(Nat.mul(d, Nat.mod(n, 1n+k)), k), cw.dm_lt(Nat.mul(l, Nat.mod(e, 1n+k)), k)))

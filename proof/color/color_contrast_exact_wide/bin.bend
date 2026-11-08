# eukhe: binary numbers for the closed contrast laws past terms of 40: the
# checker counts a Nat one successor at a time, so a product of two U32
# (up to 2^64) cannot be computed as a Nat. A list of bits, least
# significant first, can: cb.val reads it as the Nat it is, a Word's bits
# read as its Word.to_nat (cb.to_nat), and the sum (cb.addc), product
# (cb.mul) and comparison (cb.cmp) of bit lists are those of their values.

import Base
import ../../base/nat.bend as LNat

# Values
# ------

# the bit b below twice x
def cb.B(b: Bool, x: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(x)
    case True{}:
      1n+Nat.double(x)

# the value of bits, least significant first
def cb.val(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{b, t}:
      cb.B(b, cb.val(t))

# the bits of a word, least significant first
def cb.bits(n: Nat, w: Word(n)) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Con{b, cb.bits(p, t)}

def cb.u32(x: U32) -> List<&2, Bool>:
  match x:
    case U32{w}:
      cb.bits(32n, w)

def cb.to_nat(n: Nat, w: Word(n)) -> {Word.to_nat(n, w) == cb.val(cb.bits(n, w)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Nat, Nat, z => Nat.double(z), Word.to_nat(p, t), cb.val(cb.bits(p, t)), cb.to_nat(p, t))
        case WCon{True{}, t}:
          Equal.cong(Nat, Nat, z => 1n+Nat.double(z), Word.to_nat(p, t), cb.val(cb.bits(p, t)), cb.to_nat(p, t))

def cb.u32_nat(x: U32) -> {U32.to_nat(x) == cb.val(cb.u32(x)) : Nat}:
  match x:
    case U32{w}:
      cb.to_nat(32n, w)

# Comparison
# ----------

# the higher bits decide, the low bit on a tie
def cb.cmp_step(x: Nat, y: Nat, a: Bool, b: Bool) -> {Nat.cmp(cb.B(a, x), cb.B(b, y)) == Word.cmp.fin(a, b, Nat.cmp(x, y)) : Cmp}:
  match x y:
    case 0n 0n:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+q:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 0n:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n++p 1n++q:
      match a b:
        case False{} False{}:
          cb.cmp_step(p, q, False{}, False{})
        case False{} True{}:
          cb.cmp_step(p, q, False{}, True{})
        case True{} False{}:
          cb.cmp_step(p, q, True{}, False{})
        case True{} True{}:
          cb.cmp_step(p, q, True{}, True{})

# the comparison of two bit lists, the shorter padded with zeros
def cb.cmp(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Cmp:
  match xs ys:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{b, t}:
      Word.cmp.fin(False{}, b, cb.cmp(Nil{}, t))
    case Con{a, s} Nil{}:
      Word.cmp.fin(a, False{}, cb.cmp(s, Nil{}))
    case Con{a, s} Con{b, t}:
      Word.cmp.fin(a, b, cb.cmp(s, t))

def cb.cmp_val(xs: List<&2, Bool>, ys: List<&2, Bool>) -> {Nat.cmp(cb.val(xs), cb.val(ys)) == cb.cmp(xs, ys) : Cmp}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +t}:
      %cb.cmp_val(Nil{}, t) : {Nat.cmp(0n, cb.B(b, cb.val(t))) == Word.cmp.fin(False{}, b, _) : Cmp}
      cb.cmp_step(0n, cb.val(t), False{}, b)
    case Con{+a, +s} Nil{}:
      %cb.cmp_val(s, Nil{}) : {Nat.cmp(cb.B(a, cb.val(s)), 0n) == Word.cmp.fin(a, False{}, _) : Cmp}
      cb.cmp_step(cb.val(s), 0n, a, False{})
    case Con{+a, +s} Con{+b, +t}:
      %cb.cmp_val(s, t) : {Nat.cmp(cb.B(a, cb.val(s)), cb.B(b, cb.val(t))) == Word.cmp.fin(a, b, _) : Cmp}
      cb.cmp_step(cb.val(s), cb.val(t), a, b)

# Doubling
# --------

# 2x = x + x
def cb.dbl(x: Nat) -> {Nat.double(x) == Nat.add(x, x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat, 2n+Nat.double(p), 2n+Nat.add(p, p), 1n+Nat.add(p, 1n+p),
        Equal.cong(Nat, Nat, z => 2n+z, Nat.double(p), Nat.add(p, p), cb.dbl(p)),
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(p, p), Nat.add(p, 1n+p), Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), LNat.add_succ(p, p))))

# 2(x + y) = 2x + 2y
def cb.dbl_add(x: Nat, +y: Nat) -> {Nat.double(Nat.add(x, y)) == Nat.add(Nat.double(x), Nat.double(y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 2n+z, Nat.double(Nat.add(p, y)), Nat.add(Nat.double(p), Nat.double(y)), cb.dbl_add(p, y))

# (2t)·y = 2(t·y)
def cb.mul_dbl(t: Nat, +y: Nat) -> {Nat.mul(Nat.double(t), y) == Nat.double(Nat.mul(t, y)) : Nat}:
  match t:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat, Nat.add(y, Nat.add(y, Nat.mul(Nat.double(p), y))), Nat.add(y, Nat.add(y, Nat.double(Nat.mul(p, y)))), Nat.double(Nat.add(y, Nat.mul(p, y))),
        Equal.cong(Nat, Nat, z => Nat.add(y, Nat.add(y, z)), Nat.mul(Nat.double(p), y), Nat.double(Nat.mul(p, y)), cb.mul_dbl(p, y)),
        Equal.trans(Nat, Nat.add(y, Nat.add(y, Nat.double(Nat.mul(p, y)))), Nat.add(Nat.add(y, y), Nat.double(Nat.mul(p, y))), Nat.double(Nat.add(y, Nat.mul(p, y))),
          LNat.add_assoc_r(y, y, Nat.double(Nat.mul(p, y))),
          Equal.trans(Nat, Nat.add(Nat.add(y, y), Nat.double(Nat.mul(p, y))), Nat.add(Nat.double(y), Nat.double(Nat.mul(p, y))), Nat.double(Nat.add(y, Nat.mul(p, y))),
            Equal.cong(Nat, Nat, z => Nat.add(z, Nat.double(Nat.mul(p, y))), Nat.add(y, y), Nat.double(y), Equal.sym(Nat, Nat.double(y), Nat.add(y, y), cb.dbl(y))),
            Equal.sym(Nat, Nat.double(Nat.add(y, Nat.mul(p, y))), Nat.add(Nat.double(y), Nat.double(Nat.mul(p, y))), cb.dbl_add(y, Nat.mul(p, y))))))

# Sum
# ---

# xs + 1
def cb.inc(xs: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      [True{}]
    case Con{False{}, t}:
      Con{True{}, t}
    case Con{True{}, t}:
      Con{False{}, cb.inc(t)}

def cb.inc_val(xs: List<&2, Bool>) -> {cb.val(cb.inc(xs)) == 1n+cb.val(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{False{}, t}:
      {==}
    case Con{True{}, t}:
      Equal.cong(Nat, Nat, z => Nat.double(z), cb.val(cb.inc(t)), 1n+cb.val(t), cb.inc_val(t))

# xs + ys + c, bit by bit with the carry
def cb.addc(xs: List<&2, Bool>, ys: List<&2, Bool>, c: Bool) -> List<&2, Bool>:
  match xs ys c:
    case Nil{} Nil{} False{}:
      Nil{}
    case Nil{} Nil{} True{}:
      [True{}]
    case Nil{} Con{False{}, t} False{}:
      Con{False{}, t}
    case Nil{} Con{True{}, t} False{}:
      Con{True{}, t}
    case Nil{} Con{False{}, t} True{}:
      cb.inc(Con{False{}, t})
    case Nil{} Con{True{}, t} True{}:
      cb.inc(Con{True{}, t})
    case Con{False{}, s} Nil{} False{}:
      Con{False{}, s}
    case Con{True{}, s} Nil{} False{}:
      Con{True{}, s}
    case Con{False{}, s} Nil{} True{}:
      cb.inc(Con{False{}, s})
    case Con{True{}, s} Nil{} True{}:
      cb.inc(Con{True{}, s})
    case Con{False{}, s} Con{False{}, t} False{}:
      Con{False{}, cb.addc(s, t, False{})}
    case Con{False{}, s} Con{False{}, t} True{}:
      Con{True{}, cb.addc(s, t, False{})}
    case Con{False{}, s} Con{True{}, t} False{}:
      Con{True{}, cb.addc(s, t, False{})}
    case Con{False{}, s} Con{True{}, t} True{}:
      Con{False{}, cb.addc(s, t, True{})}
    case Con{True{}, s} Con{False{}, t} False{}:
      Con{True{}, cb.addc(s, t, False{})}
    case Con{True{}, s} Con{False{}, t} True{}:
      Con{False{}, cb.addc(s, t, True{})}
    case Con{True{}, s} Con{True{}, t} False{}:
      Con{False{}, cb.addc(s, t, True{})}
    case Con{True{}, s} Con{True{}, t} True{}:
      Con{True{}, cb.addc(s, t, True{})}

# 1 + 2(x + y) = 2x + (1 + 2y)
def cb.ar1(+x: Nat, +y: Nat) -> {1n+Nat.double(Nat.add(x, y)) == Nat.add(Nat.double(x), 1n+Nat.double(y)) : Nat}:
  Equal.trans(Nat, 1n+Nat.double(Nat.add(x, y)), 1n+Nat.add(Nat.double(x), Nat.double(y)), Nat.add(Nat.double(x), 1n+Nat.double(y)),
    Equal.cong(Nat, Nat, z => 1n+z, Nat.double(Nat.add(x, y)), Nat.add(Nat.double(x), Nat.double(y)), cb.dbl_add(x, y)),
    Equal.sym(Nat, Nat.add(Nat.double(x), 1n+Nat.double(y)), 1n+Nat.add(Nat.double(x), Nat.double(y)), LNat.add_succ(Nat.double(x), Nat.double(y))))

# one column of the sum: sum bit s, carry k
def cb.col(+s: Bool, k: Bool, -X: Nat, -Y: Nat, -R: Nat, -V: Nat, ih: {V == Nat.add(cb.B(k, 0n), Nat.add(X, Y)) : Nat}, ar: {cb.B(s, Nat.add(cb.B(k, 0n), Nat.add(X, Y))) == R : Nat}) -> {cb.B(s, V) == R : Nat}:
  Equal.trans(Nat, cb.B(s, V), cb.B(s, Nat.add(cb.B(k, 0n), Nat.add(X, Y))), R,
    Equal.cong(Nat, Nat, z => cb.B(s, z), V, Nat.add(cb.B(k, 0n), Nat.add(X, Y)), ih),
    ar)

def cb.addc_val(xs: List<&2, Bool>, ys: List<&2, Bool>, c: Bool) -> {cb.val(cb.addc(xs, ys, c)) == Nat.add(cb.B(c, 0n), Nat.add(cb.val(xs), cb.val(ys))) : Nat}:
  match xs ys c:
    case Nil{} Nil{} False{}:
      {==}
    case Nil{} Nil{} True{}:
      {==}
    case Nil{} Con{False{}, +t} False{}:
      {==}
    case Nil{} Con{True{}, +t} False{}:
      {==}
    case Nil{} Con{False{}, +t} True{}:
      cb.inc_val(Con{False{}, t})
    case Nil{} Con{True{}, +t} True{}:
      cb.inc_val(Con{True{}, t})
    case Con{False{}, +s} Nil{} False{}:
      Equal.sym(Nat, Nat.add(cb.val(Con{False{}, s}), 0n), cb.val(Con{False{}, s}), LNat.add_zero(cb.val(Con{False{}, s})))
    case Con{True{}, +s} Nil{} False{}:
      Equal.sym(Nat, Nat.add(cb.val(Con{True{}, s}), 0n), cb.val(Con{True{}, s}), LNat.add_zero(cb.val(Con{True{}, s})))
    case Con{False{}, +s} Nil{} True{}:
      Equal.trans(Nat, cb.val(cb.inc(Con{False{}, s})), 1n+cb.val(Con{False{}, s}), 1n+Nat.add(cb.val(Con{False{}, s}), 0n),
        cb.inc_val(Con{False{}, s}),
        Equal.cong(Nat, Nat, z => 1n+z, cb.val(Con{False{}, s}), Nat.add(cb.val(Con{False{}, s}), 0n), Equal.sym(Nat, Nat.add(cb.val(Con{False{}, s}), 0n), cb.val(Con{False{}, s}), LNat.add_zero(cb.val(Con{False{}, s})))))
    case Con{True{}, +s} Nil{} True{}:
      Equal.trans(Nat, cb.val(cb.inc(Con{True{}, s})), 1n+cb.val(Con{True{}, s}), 1n+Nat.add(cb.val(Con{True{}, s}), 0n),
        cb.inc_val(Con{True{}, s}),
        Equal.cong(Nat, Nat, z => 1n+z, cb.val(Con{True{}, s}), Nat.add(cb.val(Con{True{}, s}), 0n), Equal.sym(Nat, Nat.add(cb.val(Con{True{}, s}), 0n), cb.val(Con{True{}, s}), LNat.add_zero(cb.val(Con{True{}, s})))))
    case Con{False{}, +s} Con{False{}, +t} False{}:
      cb.col(False{}, False{}, cb.val(s), cb.val(t), Nat.add(0n, Nat.add(Nat.double(cb.val(s)), Nat.double(cb.val(t)))), cb.val(cb.addc(s, t, False{})), cb.addc_val(s, t, False{}),
        cb.dbl_add(cb.val(s), cb.val(t)))
    case Con{False{}, +s} Con{False{}, +t} True{}:
      cb.col(True{}, False{}, cb.val(s), cb.val(t), Nat.add(1n, Nat.add(Nat.double(cb.val(s)), Nat.double(cb.val(t)))), cb.val(cb.addc(s, t, False{})), cb.addc_val(s, t, False{}),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.double(Nat.add(cb.val(s), cb.val(t))), Nat.add(Nat.double(cb.val(s)), Nat.double(cb.val(t))), cb.dbl_add(cb.val(s), cb.val(t))))
    case Con{False{}, +s} Con{True{}, +t} False{}:
      cb.col(True{}, False{}, cb.val(s), cb.val(t), Nat.add(0n, Nat.add(Nat.double(cb.val(s)), 1n+Nat.double(cb.val(t)))), cb.val(cb.addc(s, t, False{})), cb.addc_val(s, t, False{}),
        cb.ar1(cb.val(s), cb.val(t)))
    case Con{False{}, +s} Con{True{}, +t} True{}:
      cb.col(False{}, True{}, cb.val(s), cb.val(t), Nat.add(1n, Nat.add(Nat.double(cb.val(s)), 1n+Nat.double(cb.val(t)))), cb.val(cb.addc(s, t, True{})), cb.addc_val(s, t, True{}),
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.double(Nat.add(cb.val(s), cb.val(t))), Nat.add(Nat.double(cb.val(s)), 1n+Nat.double(cb.val(t))), cb.ar1(cb.val(s), cb.val(t))))
    case Con{True{}, +s} Con{False{}, +t} False{}:
      cb.col(True{}, False{}, cb.val(s), cb.val(t), Nat.add(0n, Nat.add(1n+Nat.double(cb.val(s)), Nat.double(cb.val(t)))), cb.val(cb.addc(s, t, False{})), cb.addc_val(s, t, False{}),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.double(Nat.add(cb.val(s), cb.val(t))), Nat.add(Nat.double(cb.val(s)), Nat.double(cb.val(t))), cb.dbl_add(cb.val(s), cb.val(t))))
    case Con{True{}, +s} Con{False{}, +t} True{}:
      cb.col(False{}, True{}, cb.val(s), cb.val(t), Nat.add(1n, Nat.add(1n+Nat.double(cb.val(s)), Nat.double(cb.val(t)))), cb.val(cb.addc(s, t, True{})), cb.addc_val(s, t, True{}),
        Equal.cong(Nat, Nat, z => 2n+z, Nat.double(Nat.add(cb.val(s), cb.val(t))), Nat.add(Nat.double(cb.val(s)), Nat.double(cb.val(t))), cb.dbl_add(cb.val(s), cb.val(t))))
    case Con{True{}, +s} Con{True{}, +t} False{}:
      cb.col(False{}, True{}, cb.val(s), cb.val(t), Nat.add(0n, Nat.add(1n+Nat.double(cb.val(s)), 1n+Nat.double(cb.val(t)))), cb.val(cb.addc(s, t, True{})), cb.addc_val(s, t, True{}),
        Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.double(Nat.add(cb.val(s), cb.val(t))), Nat.add(Nat.double(cb.val(s)), 1n+Nat.double(cb.val(t))), cb.ar1(cb.val(s), cb.val(t))))
    case Con{True{}, +s} Con{True{}, +t} True{}:
      cb.col(True{}, True{}, cb.val(s), cb.val(t), Nat.add(1n, Nat.add(1n+Nat.double(cb.val(s)), 1n+Nat.double(cb.val(t)))), cb.val(cb.addc(s, t, True{})), cb.addc_val(s, t, True{}),
        Equal.cong(Nat, Nat, z => 2n+z, 1n+Nat.double(Nat.add(cb.val(s), cb.val(t))), Nat.add(Nat.double(cb.val(s)), 1n+Nat.double(cb.val(t))), cb.ar1(cb.val(s), cb.val(t))))

# Product
# -------

# xs · ys, shift and add
def cb.mul(xs: List<&2, Bool>, +ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{False{}, t}:
      Con{False{}, cb.mul(t, ys)}
    case Con{True{}, t}:
      cb.addc(ys, Con{False{}, cb.mul(t, ys)}, False{})

def cb.mul_val(xs: List<&2, Bool>, +ys: List<&2, Bool>) -> {cb.val(cb.mul(xs, ys)) == Nat.mul(cb.val(xs), cb.val(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{False{}, +t}:
      Equal.trans(Nat, Nat.double(cb.val(cb.mul(t, ys))), Nat.double(Nat.mul(cb.val(t), cb.val(ys))), Nat.mul(Nat.double(cb.val(t)), cb.val(ys)),
        Equal.cong(Nat, Nat, z => Nat.double(z), cb.val(cb.mul(t, ys)), Nat.mul(cb.val(t), cb.val(ys)), cb.mul_val(t, ys)),
        Equal.sym(Nat, Nat.mul(Nat.double(cb.val(t)), cb.val(ys)), Nat.double(Nat.mul(cb.val(t), cb.val(ys))), cb.mul_dbl(cb.val(t), cb.val(ys))))
    case Con{True{}, +t}:
      Equal.trans(Nat, cb.val(cb.addc(ys, Con{False{}, cb.mul(t, ys)}, False{})), Nat.add(cb.val(ys), Nat.double(cb.val(cb.mul(t, ys)))), Nat.add(cb.val(ys), Nat.mul(Nat.double(cb.val(t)), cb.val(ys))),
        cb.addc_val(ys, Con{False{}, cb.mul(t, ys)}, False{}),
        Equal.cong(Nat, Nat, z => Nat.add(cb.val(ys), z), Nat.double(cb.val(cb.mul(t, ys))), Nat.mul(Nat.double(cb.val(t)), cb.val(ys)),
          Equal.trans(Nat, Nat.double(cb.val(cb.mul(t, ys))), Nat.double(Nat.mul(cb.val(t), cb.val(ys))), Nat.mul(Nat.double(cb.val(t)), cb.val(ys)),
            Equal.cong(Nat, Nat, z => Nat.double(z), cb.val(cb.mul(t, ys)), Nat.mul(cb.val(t), cb.val(ys)), cb.mul_val(t, ys)),
            Equal.sym(Nat, Nat.mul(Nat.double(cb.val(t)), cb.val(ys)), Nat.double(Nat.mul(cb.val(t), cb.val(ys))), cb.mul_dbl(cb.val(t), cb.val(ys))))))

# Natural comparison of U32 products
# ----------------------------------

# d·n <= l·e, on the bits
def cb.le(+d: U32, +n: U32, +l: U32, +e: U32) -> Bool:
  Cmp.is_le(cb.cmp(cb.mul(cb.u32(d), cb.u32(n)), cb.mul(cb.u32(l), cb.u32(e))))

def cb.le_nat(+d: U32, +n: U32, +l: U32, +e: U32) -> {Nat.is_le(Nat.mul(U32.to_nat(d), U32.to_nat(n)), Nat.mul(U32.to_nat(l), U32.to_nat(e))) == cb.le(d, n, l, e) : Bool}:
  %Equal.sym(Nat, U32.to_nat(d), cb.val(cb.u32(d)), cb.u32_nat(d)) : {Nat.is_le(Nat.mul(_, U32.to_nat(n)), Nat.mul(U32.to_nat(l), U32.to_nat(e))) == cb.le(d, n, l, e) : Bool}
  %Equal.sym(Nat, U32.to_nat(n), cb.val(cb.u32(n)), cb.u32_nat(n)) : {Nat.is_le(Nat.mul(cb.val(cb.u32(d)), _), Nat.mul(U32.to_nat(l), U32.to_nat(e))) == cb.le(d, n, l, e) : Bool}
  %Equal.sym(Nat, U32.to_nat(l), cb.val(cb.u32(l)), cb.u32_nat(l)) : {Nat.is_le(Nat.mul(cb.val(cb.u32(d)), cb.val(cb.u32(n))), Nat.mul(_, U32.to_nat(e))) == cb.le(d, n, l, e) : Bool}
  %Equal.sym(Nat, U32.to_nat(e), cb.val(cb.u32(e)), cb.u32_nat(e)) : {Nat.is_le(Nat.mul(cb.val(cb.u32(d)), cb.val(cb.u32(n))), Nat.mul(cb.val(cb.u32(l)), _)) == cb.le(d, n, l, e) : Bool}
  %cb.mul_val(cb.u32(d), cb.u32(n)) : {Nat.is_le(_, Nat.mul(cb.val(cb.u32(l)), cb.val(cb.u32(e)))) == cb.le(d, n, l, e) : Bool}
  %cb.mul_val(cb.u32(l), cb.u32(e)) : {Nat.is_le(cb.val(cb.mul(cb.u32(d), cb.u32(n))), _) == cb.le(d, n, l, e) : Bool}
  Equal.cong(Cmp, Bool, z => Cmp.is_le(z), Nat.cmp(cb.val(cb.mul(cb.u32(d), cb.u32(n))), cb.val(cb.mul(cb.u32(l), cb.u32(e)))), cb.cmp(cb.mul(cb.u32(d), cb.u32(n)), cb.mul(cb.u32(l), cb.u32(e))), cb.cmp_val(cb.mul(cb.u32(d), cb.u32(n)), cb.mul(cb.u32(l), cb.u32(e))))

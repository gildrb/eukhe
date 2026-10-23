# eukhe: the proof of LAW wire_u32_round_trip

import Base
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def wu_nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wu_nat_eq_refl(p)

# Nat order (Nat.is_le)

def wu_le_zero(b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

def wu_le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wu_le_refl(p)

def wu_le_succ_r(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      LA.wu_absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      wu_le_succ_r(p, q, h)

def wu_le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      wu_le_zero(c)
    case 1n+p 0n c:
      LA.wu_absurd({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LA.wu_absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      wu_le_trans(p, q, r, ab, bc)

def wu_dbl_mono(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.double(a), Nat.double(b)) == True{} : Bool}:
  match a b:
    case 0n b:
      wu_le_zero(Nat.double(b))
    case 1n+p 0n:
      LA.wu_absurd({Nat.is_le(Nat.double(1n+p), 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      wu_dbl_mono(p, q, h)

# Nat.div by 10: Nat.div(n, 10n) is Pair.fst(Nat.divmod.go(n, 9n, 0n, 0n))

# the quotient of divmod.go never drops below its accumulator
def wu_go_acc(n: Nat, m: Nat, +e: Nat, +d: Nat, r: Nat, h: {Nat.is_le(e, d) == True{} : Bool}) -> {Nat.is_le(e, Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r))) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+np:
      match m:
        case 0n:
          wu_go_acc(np, r, e, 1n+d, 0n, wu_le_succ_r(e, d, h))
        case 1n+mp:
          wu_go_acc(np, mp, e, d, 1n+r, h)

# the quotient of divmod.go is monotone in the dividend
def wu_go_mono(n: Nat, k: Nat, m: Nat, +d: Nat, r: Nat, h: {Nat.is_le(n, k) == True{} : Bool}) -> {Nat.is_le(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), Pair.fst(Nat, Nat, Nat.divmod.go(k, m, d, r))) == True{} : Bool}:
  match n k:
    case 0n k:
      wu_go_acc(k, m, d, d, r, wu_le_refl(d))
    case 1n+np 0n:
      LA.wu_absurd({Nat.is_le(Pair.fst(Nat, Nat, Nat.divmod.go(1n+np, m, d, r)), d) == True{} : Bool}, h)
    case 1n+np 1n+nk:
      match m:
        case 0n:
          wu_go_mono(np, nk, r, 1n+d, 0n, h)
        case 1n+mp:
          wu_go_mono(np, nk, mp, d, 1n+r, h)

def wu_div_mono(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.div(a, 10n), Nat.div(b, 10n)) == True{} : Bool}:
  wu_go_mono(a, b, 9n, 0n, 0n, h)

# the accumulator of divmod.go adds to its quotient
def wu_go_succ(n: Nat, m: Nat, d: Nat, r: Nat) -> {Pair.fst(Nat, Nat, Nat.divmod.go(n, m, 1n+d, r)) == 1n+Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          wu_go_succ(np, r, 1n+d, 0n)
        case 1n+mp:
          wu_go_succ(np, mp, d, 1n+r)

# 10 * x + 9
def wu_t10(x: Nat) -> Nat:
  match x:
    case 0n:
      9n
    case 1n+p:
      10n+wu_t10(p)

# (10 * x + 9) / 10 == x
def wu_div_t10(+x: Nat) -> {Nat.div(wu_t10(x), 10n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      +t = wu_t10(p)
      %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(t, 9n, 1n, 0n)), 1n+Pair.fst(Nat, Nat, Nat.divmod.go(t, 9n, 0n, 0n)), wu_go_succ(t, 9n, 0n, 0n)) : {_ == 1n+p : Nat}
      %wu_div_t10(p) : {1n+Nat.div(t, 10n) == 1n+_ : Nat}
      {==}

# rewrite the upper bound of an is_le fact
def wu_le_rw(-a: Nat, -b: Nat, -c: Nat, h: {Nat.is_le(a, b) == True{} : Bool}, e: {b == c : Nat}) -> {Nat.is_le(a, c) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  h

# 10^e - 1: the largest Nat of e digits
def wu_nines(e: Nat) -> Nat:
  match e:
    case 0n:
      0n
    case 1n+d:
      wu_t10(wu_nines(d))

# a higher part q below 10^e adds at most e digits (whatever the fuel)
def wu_go_le(f: Nat, +q: Nat, +e: Nat, h: {Nat.is_le(q, wu_nines(e)) == True{} : Bool}) -> {Nat.is_le(Laws.wire_digits.go(f, q), e) == True{} : Bool}:
  match f q e:
    case 0n q e:
      wu_le_zero(e)
    case 1n+g 0n e:
      wu_le_zero(e)
    case 1n+g 1n+p 0n:
      LA.wu_absurd({Nat.is_le(Laws.wire_digits.go(1n+g, 1n+p), 0n) == True{} : Bool}, h)
    case 1n+g 1n+p 1n+d:
      +n = wu_nines(d)
      wu_go_le(g, Nat.div(1n+p, 10n), d, wu_le_rw(Nat.div(1n+p, 10n), Nat.div(wu_t10(n), 10n), n, wu_div_mono(1n+p, wu_t10(n), h), wu_div_t10(n)))

# a Nat at most 10^(1+e) - 1 has at most 1+e digits
def wu_digits_le(+n: Nat, +e: Nat, h: {Nat.is_le(n, wu_nines(1n+e)) == True{} : Bool}) -> {Nat.is_le(Laws.wire_digits(n), 1n+e) == True{} : Bool}:
  +m = wu_nines(e)
  wu_go_le(n, Nat.div(n, 10n), e, wu_le_rw(Nat.div(n, 10n), Nat.div(wu_t10(m), 10n), m, wu_div_mono(n, wu_t10(m), h), wu_div_t10(m)))

# a word of 3j + r bits (r < 3) has at most 1+j decimal digits
def wu_bd(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n:
      0n
    case 2n:
      0n
    case 3n+j:
      1n+wu_bd(j)

# one more bit: 2x + b <= 2z + 1 when x <= z
def wu_wcon_le(+p: Nat, b: Bool, +t: Word(p), +z: Nat, h: {Nat.is_le(Word.to_nat(p, t), z) == True{} : Bool}) -> {Nat.is_le(Word.to_nat(1n+p, WCon{b, t}), 1n+Nat.double(z)) == True{} : Bool}:
  match b:
    case False{}:
      wu_le_succ_r(Nat.double(Word.to_nat(p, t)), Nat.double(z), wu_dbl_mono(Word.to_nat(p, t), z, h))
    case True{}:
      wu_dbl_mono(Word.to_nat(p, t), z, h)

# 8x + 7 <= 10x + 9
def wu_87(+x: Nat) -> {Nat.is_le(1n+Nat.double(1n+Nat.double(1n+Nat.double(x))), wu_t10(x)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      +l = {1n+Nat.double(1n+Nat.double(1n+Nat.double(p))) : Nat}
      wu_le_succ_r(l, 1n+wu_t10(p), wu_le_succ_r(l, wu_t10(p), wu_87(p)))

# a word of k bits is at most 10^(1+bd(k)) - 1
def wu_word_le(+k: Nat, +w: Word(k)) -> {Nat.is_le(Word.to_nat(k, w), wu_nines(1n+wu_bd(k))) == True{} : Bool}:
  match k:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, t}:
          {==}
    case 2n:
      match w:
        case WCon{False{}, WCon{False{}, t}}:
          {==}
        case WCon{False{}, WCon{True{}, t}}:
          {==}
        case WCon{True{}, WCon{False{}, t}}:
          {==}
        case WCon{True{}, WCon{True{}, t}}:
          {==}
    case 3n+j:
      match w:
        case WCon{b0, WCon{b1, WCon{b2, t}}}:
          +n = {wu_nines(1n+wu_bd(j)) : Nat}
          +z2 = {1n+Nat.double(n) : Nat}
          +z1 = {1n+Nat.double(z2) : Nat}
          +z0 = {1n+Nat.double(z1) : Nat}
          s2 = wu_wcon_le(j, b2, t, n, wu_word_le(j, t))
          s1 = wu_wcon_le(1n+j, b1, WCon{b2, t}, z2, s2)
          s0 = wu_wcon_le(2n+j, b0, WCon{b1, WCon{b2, t}}, z1, s1)
          wu_le_trans(Word.to_nat(3n+j, WCon{b0, WCon{b1, WCon{b2, t}}}), z0, wu_t10(n), s0, wu_87(n))

# every 32-bit word fits the wire (at most 11 digits), with no 2^32 computed
def wu_u32_fits(+w: Word(32n)) -> {Laws.wire_fits(Word.to_nat(32n, w)) == True{} : Bool}:
  +n = Word.to_nat(32n, w)
  wu_le_trans(Laws.wire_digits(n), 1n+wu_bd(32n), 14n, wu_digits_le(n, wu_bd(32n), wu_word_le(32n, w)), {==})

# U32.from_nat inverts U32.to_nat

# Word.inc applied m times to the zero word of k bits
def wu_iter(+k: Nat, m: Nat) -> Word(k):
  match m:
    case 0n:
      Word.zero(k)
    case 1n+p:
      Word.inc(k, wu_iter(k, p))

def wu_from_nat(+m: Nat) -> {U32.from_nat(m) == U32{wu_iter(32n, m)} : U32}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(U32, U32.from_nat(p), U32{wu_iter(32n, p)}, wu_from_nat(p)) : {U32.inc(_) == U32{Word.inc(32n, wu_iter(32n, p))} : U32}
      {==}

# 2m increments of a word of 1+p bits: bit 0 low, m increments above
def wu_iter_even(+p: Nat, +m: Nat) -> {wu_iter(1n+p, Nat.double(m)) == WCon{False{}, wu_iter(p, m)} : Word(1n+p)}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Word(1n+p), wu_iter(1n+p, Nat.double(q)), WCon{False{}, wu_iter(p, q)}, wu_iter_even(p, q)) : {Word.inc(1n+p, Word.inc(1n+p, _)) == WCon{False{}, Word.inc(p, wu_iter(p, q))} : Word(1n+p)}
      {==}

# 2m + 1 increments: bit 0 high, m increments above
def wu_iter_odd(+p: Nat, +m: Nat) -> {wu_iter(1n+p, 1n+Nat.double(m)) == WCon{True{}, wu_iter(p, m)} : Word(1n+p)}:
  %Equal.sym(Word(1n+p), wu_iter(1n+p, Nat.double(m)), WCon{False{}, wu_iter(p, m)}, wu_iter_even(p, m)) : {Word.inc(1n+p, _) == WCon{True{}, wu_iter(p, m)} : Word(1n+p)}
  {==}

# Word.to_nat(k, w) increments of zero give w back
def wu_iter_to_nat(+k: Nat, +w: Word(k)) -> {wu_iter(k, Word.to_nat(k, w)) == w : Word(k)}:
  match k:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          %Equal.sym(Word(1n+p), wu_iter(1n+p, Nat.double(Word.to_nat(p, t))), WCon{False{}, wu_iter(p, Word.to_nat(p, t))}, wu_iter_even(p, Word.to_nat(p, t))) : {_ == WCon{False{}, t} : Word(1n+p)}
          %wu_iter_to_nat(p, t) : {WCon{False{}, wu_iter(p, Word.to_nat(p, t))} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, t}:
          %Equal.sym(Word(1n+p), wu_iter(1n+p, 1n+Nat.double(Word.to_nat(p, t))), WCon{True{}, wu_iter(p, Word.to_nat(p, t))}, wu_iter_odd(p, Word.to_nat(p, t))) : {_ == WCon{True{}, t} : Word(1n+p)}
          %wu_iter_to_nat(p, t) : {WCon{True{}, wu_iter(p, Word.to_nat(p, t))} == WCon{True{}, _} : Word(1n+p)}
          {==}

def wu_from_to(+w: Word(32n)) -> {U32.from_nat(Word.to_nat(32n, w)) == U32{w} : U32}:
  +n = Word.to_nat(32n, w)
  %Equal.sym(U32, U32.from_nat(n), U32{wu_iter(32n, n)}, wu_from_nat(n)) : {_ == U32{w} : U32}
  %wu_iter_to_nat(32n, w) : {U32{wu_iter(32n, n)} == U32{_} : U32}
  {==}

# laws of the other slices used here (filled by their provers)
def Laws.wire_u32_round_trip(x, rest):
  match x:
    case U32{w}:
      +n = Word.to_nat(32n, w)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Laws.wire_nat_round_trip(n, rest, wu_u32_fits(w))) : {Wr.get_u32.fit(_) == Wr.Got{U32{w}, rest} : Wr.Dec<U32>}
      %Equal.sym(U32, U32.from_nat(n), U32{w}, wu_from_to(w)) : {Wr.get_u32.in(Nat.is_eq(U32.to_nat(_), n), _, rest) == Wr.Got{U32{w}, rest} : Wr.Dec<U32>}
      %Equal.sym(Bool, Nat.is_eq(n, n), True{}, wu_nat_eq_refl(n)) : {Wr.get_u32.in(_, U32{w}, rest) == Wr.Got{U32{w}, rest} : Wr.Dec<U32>}
      {==}

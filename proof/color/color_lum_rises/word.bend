# eukhe: U32 arithmetic for LAW color_lum_rises, read on naturals: the
# order of two words is the order of their values (lr.le); the sum of two
# words and a carry is their value plus 2^n when the last column carries
# (lr.full, bit by bit, the column identities of cb.addc_val), so a sum
# whose last column does not carry is the sum of the values (lr.adc_nc,
# lr.addU); a sum of smaller values carries no more than one that does not
# carry (lr.cy_mono, lr.cy_monoU). No 2^32 is ever computed: the carry of a
# closed sum is a walk of 32 bits.

import Base
import ../color_contrast_exact_wide/bin.bend as LCb
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/nat.bend as LNat

# Order
# -----

# the value of a word one bit longer
def lr.wb(b: Bool, -p: Nat, -t: Word(p)) -> {Word.to_nat(1n+p, WCon{b, t}) == LCb.cb.B(b, Word.to_nat(p, t)) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# two words compare as their values
def lr.cmp(+n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), lr.cmp(p, at, bt)) : {Word.cmp.fin(ab, bb, _) == Nat.cmp(Word.to_nat(1n+p, WCon{ab, at}), Word.to_nat(1n+p, WCon{bb, bt})) : Cmp}
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{ab, at}), LCb.cb.B(ab, Word.to_nat(p, at)), lr.wb(ab, p, at)) : {Word.cmp.fin(ab, bb, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) == Nat.cmp(_, Word.to_nat(1n+p, WCon{bb, bt})) : Cmp}
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{bb, bt}), LCb.cb.B(bb, Word.to_nat(p, bt)), lr.wb(bb, p, bt)) : {Word.cmp.fin(ab, bb, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) == Nat.cmp(LCb.cb.B(ab, Word.to_nat(p, at)), _) : Cmp}
          Equal.sym(Cmp, Nat.cmp(LCb.cb.B(ab, Word.to_nat(p, at)), LCb.cb.B(bb, Word.to_nat(p, bt))), Word.cmp.fin(ab, bb, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))), LCb.cb.cmp_step(Word.to_nat(p, at), Word.to_nat(p, bt), ab, bb))

# x <= y on U32 is x <= y on their values
def lr.le(+x: U32, +y: U32) -> {U32.is_le(x, y) == Nat.is_le(U32.to_nat(x), U32.to_nat(y)) : Bool}:
  match x y:
    case U32{+a} U32{+b}:
      Equal.cong(Cmp, Bool, t => Cmp.is_le(t), Word.cmp(32n, a, b), Nat.cmp(Word.to_nat(32n, a), Word.to_nat(32n, b)), lr.cmp(32n, a, b))

def lr.leN(+x: U32, +y: U32, h: {U32.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(x), U32.to_nat(y)) == True{} : Bool}:
  %lr.le(x, y) : {_ == True{} : Bool}
  h

# Naturals
# --------

# a <= b and c <= d give a + c <= b + d
def lr.add_le(+a: Nat, +b: Nat, +c: Nat, +d: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      h2
    case 0n 1n++q:
      LNat.child.pc.le_trans(c, d, 1n+Nat.add(q, d), h2, LNat.child.pc.le_add(1n+q, d))
    case 1n++p 0n:
      LLogicLogic.wr_absurd({Nat.is_le(1n+Nat.add(p, c), Nat.add(0n, d)) == True{} : Bool}, h1)
    case 1n++p 1n++q:
      lr.add_le(p, q, c, d, h1, h2)

# x <= y gives k·x <= k·y
def lr.mul_le(+k: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.mul(k, x), Nat.mul(k, y)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      lr.add_le(x, y, Nat.mul(j, x), Nat.mul(j, y), h, lr.mul_le(j, x, y, h))

# 2^n
def lr.p2(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(lr.p2(p))

# P when b holds, else 0
def lr.ifp(b: Bool, P: Nat) -> Nat:
  match b:
    case True{}:
      P
    case False{}:
      0n

# below P, a low bit below twice P
def lr.dbl_lt(X: Nat, P: Nat, s: Bool, h: {Nat.is_lt(X, P) == True{} : Bool}) -> {Nat.is_lt(LCb.cb.B(s, X), Nat.double(P)) == True{} : Bool}:
  match X P:
    case 0n 0n:
      LLogicLogic.wr_absurd({Nat.is_lt(LCb.cb.B(s, 0n), Nat.double(0n)) == True{} : Bool}, h)
    case 1n+x 0n:
      LLogicLogic.wr_absurd({Nat.is_lt(LCb.cb.B(s, 1n+x), Nat.double(0n)) == True{} : Bool}, h)
    case 0n 1n+q:
      match s:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+x 1n+q:
      match s:
        case False{}:
          lr.dbl_lt(x, q, False{}, h)
        case True{}:
          lr.dbl_lt(x, q, True{}, h)

# a word's value is below 2^n
def lr.wlt(+n: Nat, w: Word(n)) -> {Nat.is_lt(Word.to_nat(n, w), lr.p2(n)) == True{} : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++p:
      match w:
        case WCon{False{}, +t}:
          lr.dbl_lt(Word.to_nat(p, t), lr.p2(p), False{}, lr.wlt(p, t))
        case WCon{True{}, +t}:
          lr.dbl_lt(Word.to_nat(p, t), lr.p2(p), True{}, lr.wlt(p, t))

# Sum
# ---

# the carry out of the last column of a + b + c
def lr.cy(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          lr.cy(p, at, bt, False{})
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          lr.cy(p, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          lr.cy(p, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          lr.cy(p, at, bt, True{})
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          lr.cy(p, at, bt, False{})
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          lr.cy(p, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          lr.cy(p, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          lr.cy(p, at, bt, True{})

# a low bit below twice (V + I) is a low bit below twice V, plus twice I
def lr.bsplit(s: Bool, +V: Nat, +I: Nat) -> {LCb.cb.B(s, Nat.add(V, I)) == Nat.add(LCb.cb.B(s, V), Nat.double(I)) : Nat}:
  match s:
    case False{}:
      LCb.cb.dbl_add(V, I)
    case True{}:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.double(Nat.add(V, I)), Nat.add(Nat.double(V), Nat.double(I)), LCb.cb.dbl_add(V, I))

def lr.dif(b: Bool, -P: Nat) -> {Nat.double(lr.ifp(b, P)) == lr.ifp(b, Nat.double(P)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# one column: sum bit s, carry k into the higher columns, R the whole sum
def lr.col(+s: Bool, +k: Bool, +p: Nat, +at: Word(p), +bt: Word(p), -R: Nat,
  ar: {LCb.cb.B(s, Nat.add(LCb.cb.B(k, 0n), Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))) == R : Nat},
  ih: {Nat.add(LCb.cb.B(k, 0n), Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt))) == Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, k)), lr.ifp(lr.cy(p, at, bt, k), lr.p2(p))) : Nat})
  -> {R == Nat.add(LCb.cb.B(s, Word.to_nat(p, Word.adc(p, at, bt, False{}, k))), lr.ifp(lr.cy(p, at, bt, k), Nat.double(lr.p2(p)))) : Nat}:
  +M = Nat.add(LCb.cb.B(k, 0n), Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))
  +V = Word.to_nat(p, Word.adc(p, at, bt, False{}, k))
  +I = lr.ifp(lr.cy(p, at, bt, k), lr.p2(p))
  Equal.trans(Nat, R, LCb.cb.B(s, M), Nat.add(LCb.cb.B(s, V), lr.ifp(lr.cy(p, at, bt, k), Nat.double(lr.p2(p)))),
    Equal.sym(Nat, LCb.cb.B(s, M), R, ar),
    Equal.trans(Nat, LCb.cb.B(s, M), LCb.cb.B(s, Nat.add(V, I)), Nat.add(LCb.cb.B(s, V), lr.ifp(lr.cy(p, at, bt, k), Nat.double(lr.p2(p)))),
      Equal.cong(Nat, Nat, z => LCb.cb.B(s, z), M, Nat.add(V, I), ih),
      Equal.trans(Nat, LCb.cb.B(s, Nat.add(V, I)), Nat.add(LCb.cb.B(s, V), Nat.double(I)), Nat.add(LCb.cb.B(s, V), lr.ifp(lr.cy(p, at, bt, k), Nat.double(lr.p2(p)))),
        lr.bsplit(s, V, I),
        Equal.cong(Nat, Nat, z => Nat.add(LCb.cb.B(s, V), z), Nat.double(I), lr.ifp(lr.cy(p, at, bt, k), Nat.double(lr.p2(p))), lr.dif(lr.cy(p, at, bt, k), lr.p2(p))))))

# the sum of two words and a carry is the word's value plus 2^n when the
# last column carries
def lr.full(+n: Nat, a: Word(n), b: Word(n), c: Bool) -> {Nat.add(LCb.cb.B(c, 0n), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) == Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), lr.ifp(lr.cy(n, a, b, c), lr.p2(n))) : Nat}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} False{}:
          {==}
        case WNil{} WNil{} True{}:
          {==}
    case 1n++p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          lr.col(False{}, False{}, p, at, bt, Nat.add(0n, Nat.add(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt)))),
            LCb.cb.dbl_add(Word.to_nat(p, at), Word.to_nat(p, bt)), lr.full(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          lr.col(True{}, False{}, p, at, bt, Nat.add(1n, Nat.add(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt)))),
            Equal.cong(Nat, Nat, z => 1n+z, Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.add(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))), LCb.cb.dbl_add(Word.to_nat(p, at), Word.to_nat(p, bt))), lr.full(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          lr.col(True{}, False{}, p, at, bt, Nat.add(0n, Nat.add(Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt)))),
            LCb.cb.ar1(Word.to_nat(p, at), Word.to_nat(p, bt)), lr.full(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          lr.col(False{}, True{}, p, at, bt, Nat.add(1n, Nat.add(Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt)))),
            Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.add(Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt))), LCb.cb.ar1(Word.to_nat(p, at), Word.to_nat(p, bt))), lr.full(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          lr.col(True{}, False{}, p, at, bt, Nat.add(0n, Nat.add(1n+Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt)))),
            Equal.cong(Nat, Nat, z => 1n+z, Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.add(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))), LCb.cb.dbl_add(Word.to_nat(p, at), Word.to_nat(p, bt))), lr.full(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          lr.col(False{}, True{}, p, at, bt, Nat.add(1n, Nat.add(1n+Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt)))),
            Equal.cong(Nat, Nat, z => 2n+z, Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.add(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))), LCb.cb.dbl_add(Word.to_nat(p, at), Word.to_nat(p, bt))), lr.full(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          lr.col(False{}, True{}, p, at, bt, Nat.add(0n, Nat.add(1n+Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt)))),
            Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.add(Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt))), LCb.cb.ar1(Word.to_nat(p, at), Word.to_nat(p, bt))), lr.full(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          lr.col(True{}, True{}, p, at, bt, Nat.add(1n, Nat.add(1n+Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt)))),
            Equal.cong(Nat, Nat, z => 2n+z, 1n+Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.add(Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt))), LCb.cb.ar1(Word.to_nat(p, at), Word.to_nat(p, bt))), lr.full(p, at, bt, True{}))

# a sum whose last column does not carry: the word's value plus 0
def lr.full_nc(+n: Nat, +a: Word(n), +b: Word(n), +c: Bool, h: {lr.cy(n, a, b, c) == False{} : Bool}) -> {Nat.add(LCb.cb.B(c, 0n), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) == Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), 0n) : Nat}:
  %h : {Nat.add(LCb.cb.B(c, 0n), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) == Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), lr.ifp(_, lr.p2(n))) : Nat}
  lr.full(n, a, b, c)

# a sum whose last column does not carry is the sum of the values
def lr.adc_nc(+n: Nat, +a: Word(n), +b: Word(n), +c: Bool, h: {lr.cy(n, a, b, c) == False{} : Bool}) -> {Word.to_nat(n, Word.adc(n, a, b, False{}, c)) == Nat.add(LCb.cb.B(c, 0n), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) : Nat}:
  +V = Word.to_nat(n, Word.adc(n, a, b, False{}, c))
  Equal.sym(Nat, Nat.add(LCb.cb.B(c, 0n), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))), V,
    Equal.trans(Nat, Nat.add(LCb.cb.B(c, 0n), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))), Nat.add(V, 0n), V, lr.full_nc(n, a, b, c, h), LNat.add_zero(V)))

# a carry out of S = V + P with S <= S2 = V2 < P is impossible
def lr.cy_no(t: Bool, +S: Nat, +V: Nat, +P: Nat, +S2: Nat, +V2: Nat, e: {S == Nat.add(V, lr.ifp(t, P)) : Nat}, e2: {S2 == Nat.add(V2, 0n) : Nat}, hv2: {Nat.is_lt(V2, P) == True{} : Bool}, hle: {Nat.is_le(S, S2) == True{} : Bool}) -> {t == False{} : Bool}:
  match t:
    case False{}:
      {==}
    case True{}:
      +hP = LNat.child.pc.le_trans(P, S, S2, Equal.trans(Bool, Nat.is_le(P, S), Nat.is_le(P, Nat.add(V, P)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(P, z), S, Nat.add(V, P), e), LNat.child.pc.le_add(V, P)), hle)
      +hS2 = Equal.trans(Bool, Nat.is_lt(S2, P), Nat.is_lt(V2, P), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, P), S2, V2, Equal.trans(Nat, S2, Nat.add(V2, 0n), V2, e2, LNat.add_zero(V2))), hv2)
      LLogicLogic.wr_absurd({True{} == False{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(P, P), True{}, Equal.sym(Bool, Nat.is_lt(P, P), False{}, LNat.pt.lt_irrefl(P)), LNat.pc.le_lt_trans(P, S2, P, hP, hS2)))

# a sum of values at most those of a sum that does not carry does not carry
def lr.cy_mono(+n: Nat, +a: Word(n), +b: Word(n), +a2: Word(n), +b2: Word(n), +c: Bool, ha: {Nat.is_le(Word.to_nat(n, a), Word.to_nat(n, a2)) == True{} : Bool}, hb: {Nat.is_le(Word.to_nat(n, b), Word.to_nat(n, b2)) == True{} : Bool}, h2: {lr.cy(n, a2, b2, c) == False{} : Bool}) -> {lr.cy(n, a, b, c) == False{} : Bool}:
  +C = LCb.cb.B(c, 0n)
  lr.cy_no(lr.cy(n, a, b, c), Nat.add(C, Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))), Word.to_nat(n, Word.adc(n, a, b, False{}, c)), lr.p2(n), Nat.add(C, Nat.add(Word.to_nat(n, a2), Word.to_nat(n, b2))), Word.to_nat(n, Word.adc(n, a2, b2, False{}, c)),
    lr.full(n, a, b, c),
    lr.full_nc(n, a2, b2, c, h2),
    lr.wlt(n, Word.adc(n, a2, b2, False{}, c)),
    lr.add_le(C, C, Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.add(Word.to_nat(n, a2), Word.to_nat(n, b2)), LNat.child.pc.le_refl(C), lr.add_le(Word.to_nat(n, a), Word.to_nat(n, a2), Word.to_nat(n, b), Word.to_nat(n, b2), ha, hb)))

# U32
# ---

# the carry out of x + y
def lr.cyU(x: U32, y: U32) -> Bool:
  match x y:
    case U32{a} U32{b}:
      lr.cy(32n, a, b, False{})

# x + y on U32, when it does not carry, is the sum of the values
def lr.addU(+x: U32, +y: U32, h: {lr.cyU(x, y) == False{} : Bool}) -> {U32.to_nat((x + y : U32)) == Nat.add(U32.to_nat(x), U32.to_nat(y)) : Nat}:
  match x y:
    case U32{+a} U32{+b}:
      lr.adc_nc(32n, a, b, False{}, h)

# x + y does not carry when x2 + y2 does not and x, y are at most x2, y2
def lr.cy_monoU(+x: U32, +y: U32, +x2: U32, +y2: U32, hx: {Nat.is_le(U32.to_nat(x), U32.to_nat(x2)) == True{} : Bool}, hy: {Nat.is_le(U32.to_nat(y), U32.to_nat(y2)) == True{} : Bool}, h2: {lr.cyU(x2, y2) == False{} : Bool}) -> {lr.cyU(x, y) == False{} : Bool}:
  match x y x2 y2:
    case U32{+a} U32{+b} U32{+a2} U32{+b2}:
      lr.cy_mono(32n, a, b, a2, b2, False{}, hx, hy, h2)

# the sum x + y is at most X + Y when x, y are at most X, Y and neither
# sum carries
def lr.le_sum(+x: U32, +y: U32, +X: U32, +Y: U32, hx: {Nat.is_le(U32.to_nat(x), U32.to_nat(X)) == True{} : Bool}, hy: {Nat.is_le(U32.to_nat(y), U32.to_nat(Y)) == True{} : Bool}, nc: {lr.cyU(x, y) == False{} : Bool}, nC: {lr.cyU(X, Y) == False{} : Bool}) -> {Nat.is_le(U32.to_nat((x + y : U32)), U32.to_nat((X + Y : U32))) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat((x + y : U32)), Nat.add(U32.to_nat(x), U32.to_nat(y)), lr.addU(x, y, nc)) : {Nat.is_le(_, U32.to_nat((X + Y : U32))) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat((X + Y : U32)), Nat.add(U32.to_nat(X), U32.to_nat(Y)), lr.addU(X, Y, nC)) : {Nat.is_le(Nat.add(U32.to_nat(x), U32.to_nat(y)), _) == True{} : Bool}
  lr.add_le(U32.to_nat(x), U32.to_nat(X), U32.to_nat(y), U32.to_nat(Y), hx, hy)

# Products
# --------

def lr.cmp_true(+xs: List<&2, Bool>, +ys: List<&2, Bool>, h: {Cmp.is_eq(LCb.cb.cmp(xs, ys)) == True{} : Bool}) -> {Cmp.is_eq(Nat.cmp(LCb.cb.val(xs), LCb.cb.val(ys))) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(LCb.cb.val(xs), LCb.cb.val(ys)), LCb.cb.cmp(xs, ys), LCb.cb.cmp_val(xs, ys)) : {Cmp.is_eq(_) == True{} : Bool}
  h

def lr.nat_eq(+x: Nat, +y: Nat, e: {Cmp.is_eq(Nat.cmp(x, y)) == True{} : Bool}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.wr_absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      LLogicLogic.wr_absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, p, q, lr.nat_eq(p, q, e))

# k·v on U32 is k·v on the values, once the bits say so
def lr.mulv(+k: U32, +v: U32, h: {Cmp.is_eq(LCb.cb.cmp(LCb.cb.u32((k * v : U32)), LCb.cb.mul(LCb.cb.u32(k), LCb.cb.u32(v)))) == True{} : Bool}) -> {U32.to_nat((k * v : U32)) == Nat.mul(U32.to_nat(k), U32.to_nat(v)) : Nat}:
  +xs = LCb.cb.u32((k * v : U32))
  +ys = LCb.cb.mul(LCb.cb.u32(k), LCb.cb.u32(v))
  +e1 = lr.cmp_true(xs, ys, h)
  Equal.trans(Nat, U32.to_nat((k * v : U32)), LCb.cb.val(xs), Nat.mul(U32.to_nat(k), U32.to_nat(v)),
    LCb.cb.u32_nat((k * v : U32)),
    Equal.trans(Nat, LCb.cb.val(xs), LCb.cb.val(ys), Nat.mul(U32.to_nat(k), U32.to_nat(v)),
      lr.nat_eq(LCb.cb.val(xs), LCb.cb.val(ys), e1),
      Equal.trans(Nat, LCb.cb.val(ys), Nat.mul(LCb.cb.val(LCb.cb.u32(k)), LCb.cb.val(LCb.cb.u32(v))), Nat.mul(U32.to_nat(k), U32.to_nat(v)),
        LCb.cb.mul_val(LCb.cb.u32(k), LCb.cb.u32(v)),
        Equal.trans(Nat, Nat.mul(LCb.cb.val(LCb.cb.u32(k)), LCb.cb.val(LCb.cb.u32(v))), Nat.mul(U32.to_nat(k), LCb.cb.val(LCb.cb.u32(v))), Nat.mul(U32.to_nat(k), U32.to_nat(v)),
          Equal.cong(Nat, Nat, z => Nat.mul(z, LCb.cb.val(LCb.cb.u32(v))), LCb.cb.val(LCb.cb.u32(k)), U32.to_nat(k), Equal.sym(Nat, U32.to_nat(k), LCb.cb.val(LCb.cb.u32(k)), LCb.cb.u32_nat(k))),
          Equal.cong(Nat, Nat, z => Nat.mul(U32.to_nat(k), z), LCb.cb.val(LCb.cb.u32(v)), U32.to_nat(v), Equal.sym(Nat, U32.to_nat(v), LCb.cb.val(LCb.cb.u32(v)), LCb.cb.u32_nat(v)))))))

# k·x <= k·x2 on the values when x <= x2 and both products are the
# products of the values
def lr.term_le(+k: U32, +x: U32, +x2: U32, ex: {U32.to_nat((k * x : U32)) == Nat.mul(U32.to_nat(k), U32.to_nat(x)) : Nat}, ex2: {U32.to_nat((k * x2 : U32)) == Nat.mul(U32.to_nat(k), U32.to_nat(x2)) : Nat}, h: {U32.is_le(x, x2) == True{} : Bool}) -> {Nat.is_le(U32.to_nat((k * x : U32)), U32.to_nat((k * x2 : U32))) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat((k * x : U32)), Nat.mul(U32.to_nat(k), U32.to_nat(x)), ex) : {Nat.is_le(_, U32.to_nat((k * x2 : U32))) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat((k * x2 : U32)), Nat.mul(U32.to_nat(k), U32.to_nat(x2)), ex2) : {Nat.is_le(Nat.mul(U32.to_nat(k), U32.to_nat(x)), _) == True{} : Bool}
  lr.mul_le(U32.to_nat(k), U32.to_nat(x), U32.to_nat(x2), lr.leN(x, x2, h))

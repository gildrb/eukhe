# eukhe: lemmas of LAW goal_text_left_value: the subtraction
#
# The code subtracts digit strings least significant first (Gt.sub.go). On
# digit chars it is lv.sl on the digits (lv.sub_go), and the digits it
# answers are worth the first less the second plus 10^n times the borrow
# left at the end (lv.sub_value: lv.L the value of digits least
# significant first, lv.p10 the powers of 10); that borrow is 0 when the
# first is worth at least the second (lv.no_borrow).

import Base
import ../../../bend/goal_text.bend as Gt
import ../../../laws/base.bend as LawsBase
import ./nat.bend as LN
import ./digits.bend as LD

# the value of digits, least significant first
def lv.L(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> r:
      Nat.add(x, Nat.mul(10n, lv.L(r)))

def lv.p10(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+m:
      Nat.mul(10n, lv.p10(m))

# the digit of x less y less the borrow k
def lv.z(+x: Nat, +y: Nat, +k: Nat) -> Nat:
  Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n)

# the digits of ra less rb less the borrow k, as Gt.sub.go computes them
def lv.sl(ra: List<&2, Nat>, rb: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  match ra:
    case Nil{}:
      Nil{}
    case +x <> ta:
      match rb:
        case Nil{}:
          lv.z(x, 0n, k) <> lv.sl(ta, Nil{}, Gt.sub.borrow(x, 0n, k))
        case +y <> tb:
          lv.z(x, y, k) <> lv.sl(ta, tb, Gt.sub.borrow(x, y, k))

# the borrow left at the end
def lv.bo(ra: List<&2, Nat>, rb: List<&2, Nat>, +k: Nat) -> Nat:
  match ra:
    case Nil{}:
      k
    case +x <> ta:
      match rb:
        case Nil{}:
          lv.bo(ta, Nil{}, Gt.sub.borrow(x, 0n, k))
        case +y <> tb:
          lv.bo(ta, tb, Gt.sub.borrow(x, y, k))

def lv.D(xs: List<&2, Nat>) -> String:
  LawsBase.wire_digit_chars(xs, "")

# Bool
# ----

def lv.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LN.lv.absurd({False{} == True{} : Bool}, e)

def lv.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LN.lv.absurd({b == True{} : Bool}, e)

# a borrow is 0 or 1
def lv.bw_le(b: Bool) -> {Nat.is_le(Gt.sub.borrow.of(b), 1n) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a < 1 + b is a <= b
def lv.lt_succ(a: Nat, b: Nat) -> {Nat.is_lt(a, 1n+b) == Nat.is_le(a, b) : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match p:
        case 0n:
          match b:
            case 0n:
              {==}
            case 1n+q:
              lv.lt_succ(0n, q)
        case 1n+r:
          match b:
            case 0n:
              {==}
            case 1n+q:
              lv.lt_succ(1n+r, q)

def lv.lt_le(+a: Nat, +b: Nat, h: {Nat.is_lt(a, 1n+b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(a, b), Nat.is_lt(a, 1n+b), True{}, Equal.sym(Bool, Nat.is_lt(a, 1n+b), Nat.is_le(a, b), lv.lt_succ(a, b)), h)

def lv.le_lt(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(a, 1n+b), Nat.is_le(a, b), True{}, lv.lt_succ(a, b), h)

# y + k is at most 10 when y is a digit and k at most 1
def lv.yk(+y: Nat, +k: Nat, hy: {Nat.is_lt(y, 10n) == True{} : Bool}, hk: {Nat.is_le(k, 1n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(y, k), 11n) == True{} : Bool}:
  lv.le_lt(Nat.add(y, k), 10n, LN.lv.add_le(y, 9n, k, 1n, lv.lt_le(y, 9n, hy), hk))

def lv.fst(-A: Type, -B: Type, p: (A & B)) -> A:
  (a, b) = p
  a

def lv.snd(-A: Type, -B: Type, p: (A & B)) -> B:
  (a, b) = p
  b

# Gt.sub.go on digit chars
# ------------------------

def lv.sub_go(ra: List<&2, Nat>, rb: List<&2, Nat>, +k: Nat, +ha: {LawsBase.wire_digits_all(ra) == True{} : Bool}, +hb: {LawsBase.wire_digits_all(rb) == True{} : Bool}, hk: {Nat.is_le(k, 1n) == True{} : Bool}) -> {Gt.sub.go(lv.D(ra), lv.D(rb), k) == lv.D(lv.sl(ra, rb, k)) : String}:
  match ra:
    case Nil{}:
      {==}
    case +x <> +ta:
      match rb:
        case Nil{}:
          +hx = lv.and_l(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          +hta = lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          +c = Nat.add(0n, k)
          +ed = lv.fst({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n)) : Char}, ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n), Nat.add(0n, k)) == Nat.add(x, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(x, Nat.add(0n, k))))) : Nat}), LD.lv.t_sub(x, Nat.add(0n, k), hx, lv.yk(0n, k, {==}, hk)))
          +b = Gt.sub.borrow(x, 0n, k)
          %Equal.sym(Nat, Gt.digit(LawsBase.wire_dec_char(x)), x, LD.lv.t_digit(x, hx)) : {Gt.sub.of(_, 0n, k, Gt.sub.go(lv.D(ta), SNil{}, Gt.sub.borrow(_, 0n, k))) == lv.D(lv.sl(x <> ta, Nil{}, k)) : String}
          %Equal.sym(String, Gt.sub.go(lv.D(ta), lv.D(Nil{}), b), lv.D(lv.sl(ta, Nil{}, b)), lv.sub_go(ta, Nil{}, b, hta, {==}, lv.bw_le(Nat.is_lt(x, c)))) : {Gt.sub.of(x, 0n, k, _) == lv.D(lv.sl(x <> ta, Nil{}, k)) : String}
          %Equal.sym(Char, Gt.dchar(lv.z(x, 0n, k)), LawsBase.wire_dec_char(lv.z(x, 0n, k)), ed) : {SCon{_, lv.D(lv.sl(ta, Nil{}, b))} == lv.D(lv.sl(x <> ta, Nil{}, k)) : String}
          {==}
        case +y <> +tb:
          +hx = lv.and_l(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          +hta = lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          +hy = lv.and_l(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(tb), hb)
          +htb = lv.and_r(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(tb), hb)
          +c = Nat.add(y, k)
          +ed = lv.fst({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n)) : Char}, ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n), Nat.add(y, k)) == Nat.add(x, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(x, Nat.add(y, k))))) : Nat}), LD.lv.t_sub(x, Nat.add(y, k), hx, lv.yk(y, k, hy, hk)))
          +b = Gt.sub.borrow(x, y, k)
          %Equal.sym(Nat, Gt.digit(LawsBase.wire_dec_char(x)), x, LD.lv.t_digit(x, hx)) : {Gt.sub.of(_, Gt.digit(LawsBase.wire_dec_char(y)), k, Gt.sub.go(lv.D(ta), lv.D(tb), Gt.sub.borrow(_, Gt.digit(LawsBase.wire_dec_char(y)), k))) == lv.D(lv.sl(x <> ta, y <> tb, k)) : String}
          %Equal.sym(Nat, Gt.digit(LawsBase.wire_dec_char(y)), y, LD.lv.t_digit(y, hy)) : {Gt.sub.of(x, _, k, Gt.sub.go(lv.D(ta), lv.D(tb), Gt.sub.borrow(x, _, k))) == lv.D(lv.sl(x <> ta, y <> tb, k)) : String}
          %Equal.sym(String, Gt.sub.go(lv.D(ta), lv.D(tb), b), lv.D(lv.sl(ta, tb, b)), lv.sub_go(ta, tb, b, hta, htb, lv.bw_le(Nat.is_lt(x, c)))) : {Gt.sub.of(x, y, k, _) == lv.D(lv.sl(x <> ta, y <> tb, k)) : String}
          %Equal.sym(Char, Gt.dchar(lv.z(x, y, k)), LawsBase.wire_dec_char(lv.z(x, y, k)), ed) : {SCon{_, lv.D(lv.sl(ta, tb, b))} == lv.D(lv.sl(x <> ta, y <> tb, k)) : String}
          {==}

# Sums
# ----

# (a + b) + c == (a + c) + b
def lv.add_rr(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), LN.lv.add_assoc(a, b, c)) : {_ == Nat.add(Nat.add(a, c), b) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), LN.lv.add_assoc(a, c, b)) : {Nat.add(a, Nat.add(b, c)) == _ : Nat}
  Equal.cong(Nat, Nat, w => Nat.add(a, w), Nat.add(b, c), Nat.add(c, b), LN.lv.add_comm(b, c))

# (a + b) + (c + d) == (a + c) + (b + d)
def lv.add_4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), LN.lv.add_assoc(a, b, Nat.add(c, d))) : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), LN.lv.add_assoc(a, c, Nat.add(b, d))) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  Equal.cong(Nat, Nat, w => Nat.add(a, w), Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), LN.lv.add_swap(b, c, d))

# b + (R + T) == R + (T + b)
def lv.bRT(+b: Nat, +R: Nat, +T: Nat) -> {Nat.add(b, Nat.add(R, T)) == Nat.add(R, Nat.add(T, b)) : Nat}:
  %LN.lv.add_comm(b, T) : {Nat.add(b, Nat.add(R, T)) == Nat.add(R, _) : Nat}
  LN.lv.add_swap(b, R, T)

# one step of the subtraction: the digit z of x less y less the borrow k
# (z + y + k == x + 10 * b), then the rest
def lv.ar(+z: Nat, +y: Nat, +k: Nat, +x: Nat, +b: Nat, +R: Nat, +T: Nat, +A: Nat, +Q: Nat, h1: {Nat.add(z, Nat.add(y, k)) == Nat.add(x, Nat.mul(10n, b)) : Nat}, h2: {Nat.add(R, Nat.add(T, b)) == Nat.add(A, Q) : Nat}) -> {Nat.add(Nat.add(z, Nat.mul(10n, R)), Nat.add(Nat.add(y, Nat.mul(10n, T)), k)) == Nat.add(Nat.add(x, Nat.mul(10n, A)), Nat.mul(10n, Q)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(z, Nat.mul(10n, R)), Nat.add(Nat.add(y, Nat.mul(10n, T)), k)), Nat.add(Nat.add(z, Nat.mul(10n, R)), Nat.add(Nat.add(y, k), Nat.mul(10n, T))), Nat.add(Nat.add(x, Nat.mul(10n, A)), Nat.mul(10n, Q)), Equal.cong(Nat, Nat, w => Nat.add(Nat.add(z, Nat.mul(10n, R)), w), Nat.add(Nat.add(y, Nat.mul(10n, T)), k), Nat.add(Nat.add(y, k), Nat.mul(10n, T)), lv.add_rr(y, Nat.mul(10n, T), k)), Equal.trans(Nat, Nat.add(Nat.add(z, Nat.mul(10n, R)), Nat.add(Nat.add(y, k), Nat.mul(10n, T))), Nat.add(Nat.add(z, Nat.add(y, k)), Nat.add(Nat.mul(10n, R), Nat.mul(10n, T))), Nat.add(Nat.add(x, Nat.mul(10n, A)), Nat.mul(10n, Q)), lv.add_4(z, Nat.mul(10n, R), Nat.add(y, k), Nat.mul(10n, T)), Equal.trans(Nat, Nat.add(Nat.add(z, Nat.add(y, k)), Nat.add(Nat.mul(10n, R), Nat.mul(10n, T))), Nat.add(Nat.add(x, Nat.mul(10n, b)), Nat.add(Nat.mul(10n, R), Nat.mul(10n, T))), Nat.add(Nat.add(x, Nat.mul(10n, A)), Nat.mul(10n, Q)), Equal.cong(Nat, Nat, w => Nat.add(w, Nat.add(Nat.mul(10n, R), Nat.mul(10n, T))), Nat.add(z, Nat.add(y, k)), Nat.add(x, Nat.mul(10n, b)), h1), Equal.trans(Nat, Nat.add(Nat.add(x, Nat.mul(10n, b)), Nat.add(Nat.mul(10n, R), Nat.mul(10n, T))), Nat.add(x, Nat.add(Nat.mul(10n, b), Nat.add(Nat.mul(10n, R), Nat.mul(10n, T)))), Nat.add(Nat.add(x, Nat.mul(10n, A)), Nat.mul(10n, Q)), LN.lv.add_assoc(x, Nat.mul(10n, b), Nat.add(Nat.mul(10n, R), Nat.mul(10n, T))), Equal.trans(Nat, Nat.add(x, Nat.add(Nat.mul(10n, b), Nat.add(Nat.mul(10n, R), Nat.mul(10n, T)))), Nat.add(x, Nat.add(Nat.mul(10n, b), Nat.mul(10n, Nat.add(R, T)))), Nat.add(Nat.add(x, Nat.mul(10n, A)), Nat.mul(10n, Q)), Equal.cong(Nat, Nat, w => Nat.add(x, Nat.add(Nat.mul(10n, b), w)), Nat.add(Nat.mul(10n, R), Nat.mul(10n, T)), Nat.mul(10n, Nat.add(R, T)), Equal.sym(Nat, Nat.mul(10n, Nat.add(R, T)), Nat.add(Nat.mul(10n, R), Nat.mul(10n, T)), LN.lv.mul_dist_l(10n, R, T))), Equal.trans(Nat, Nat.add(x, Nat.add(Nat.mul(10n, b), Nat.mul(10n, Nat.add(R, T)))), Nat.add(x, Nat.mul(10n, Nat.add(b, Nat.add(R, T)))), Nat.add(Nat.add(x, Nat.mul(10n, A)), Nat.mul(10n, Q)), Equal.cong(Nat, Nat, w => Nat.add(x, w), Nat.add(Nat.mul(10n, b), Nat.mul(10n, Nat.add(R, T))), Nat.mul(10n, Nat.add(b, Nat.add(R, T))), Equal.sym(Nat, Nat.mul(10n, Nat.add(b, Nat.add(R, T))), Nat.add(Nat.mul(10n, b), Nat.mul(10n, Nat.add(R, T))), LN.lv.mul_dist_l(10n, b, Nat.add(R, T)))), Equal.trans(Nat, Nat.add(x, Nat.mul(10n, Nat.add(b, Nat.add(R, T)))), Nat.add(x, Nat.mul(10n, Nat.add(R, Nat.add(T, b)))), Nat.add(Nat.add(x, Nat.mul(10n, A)), Nat.mul(10n, Q)), Equal.cong(Nat, Nat, w => Nat.add(x, Nat.mul(10n, w)), Nat.add(b, Nat.add(R, T)), Nat.add(R, Nat.add(T, b)), lv.bRT(b, R, T)), Equal.trans(Nat, Nat.add(x, Nat.mul(10n, Nat.add(R, Nat.add(T, b)))), Nat.add(x, Nat.mul(10n, Nat.add(A, Q))), Nat.add(Nat.add(x, Nat.mul(10n, A)), Nat.mul(10n, Q)), Equal.cong(Nat, Nat, w => Nat.add(x, Nat.mul(10n, w)), Nat.add(R, Nat.add(T, b)), Nat.add(A, Q), h2), Equal.trans(Nat, Nat.add(x, Nat.mul(10n, Nat.add(A, Q))), Nat.add(x, Nat.add(Nat.mul(10n, A), Nat.mul(10n, Q))), Nat.add(Nat.add(x, Nat.mul(10n, A)), Nat.mul(10n, Q)), Equal.cong(Nat, Nat, w => Nat.add(x, w), Nat.mul(10n, Nat.add(A, Q)), Nat.add(Nat.mul(10n, A), Nat.mul(10n, Q)), LN.lv.mul_dist_l(10n, A, Q)), Equal.sym(Nat, Nat.add(Nat.add(x, Nat.mul(10n, A)), Nat.mul(10n, Q)), Nat.add(x, Nat.add(Nat.mul(10n, A), Nat.mul(10n, Q))), LN.lv.add_assoc(x, Nat.mul(10n, A), Nat.mul(10n, Q))))))))))))

# The value of the subtraction
# ----------------------------

# the digits of ra less rb less the borrow k, plus rb and k, are worth ra
# plus 10^n times the borrow left (n the length of ra, rb no longer)
def lv.sub_value(ra: List<&2, Nat>, rb: List<&2, Nat>, +k: Nat, +ha: {LawsBase.wire_digits_all(ra) == True{} : Bool}, +hb: {LawsBase.wire_digits_all(rb) == True{} : Bool}, +hk: {Nat.is_le(k, 1n) == True{} : Bool}, hl: {Nat.is_le(List.length(&2, Nat, rb), List.length(&2, Nat, ra)) == True{} : Bool}) -> {Nat.add(lv.L(lv.sl(ra, rb, k)), Nat.add(lv.L(rb), k)) == Nat.add(lv.L(ra), Nat.mul(lv.p10(List.length(&2, Nat, ra)), lv.bo(ra, rb, k))) : Nat}:
  match ra:
    case Nil{}:
      match rb:
        case Nil{}:
          Equal.sym(Nat, Nat.add(k, 0n), k, LN.lv.add_zero(k))
        case y <> tb:
          LN.lv.absurd({Nat.add(lv.L(lv.sl(Nil{}, y <> tb, k)), Nat.add(lv.L(y <> tb), k)) == Nat.add(lv.L(Nil{}), Nat.mul(lv.p10(0n), lv.bo(Nil{}, y <> tb, k))) : Nat}, hl)
    case +x <> +ta:
      match rb:
        case Nil{}:
          +hx = lv.and_l(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          +hta = lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          +b = Gt.sub.borrow(x, 0n, k)
          +P = lv.p10(List.length(&2, Nat, ta))
          +bo = lv.bo(ta, Nil{}, b)
          +ih = lv.sub_value(ta, Nil{}, b, hta, {==}, lv.bw_le(Nat.is_lt(x, Nat.add(0n, k))), LN.lv.le_zero(List.length(&2, Nat, ta)))
          %Equal.sym(Nat, Nat.mul(Nat.mul(10n, P), bo), Nat.mul(10n, Nat.mul(P, bo)), LN.lv.mul_assoc(10n, P, bo)) : {Nat.add(lv.L(lv.sl(x <> ta, Nil{}, k)), k) == Nat.add(Nat.add(x, Nat.mul(10n, lv.L(ta))), _) : Nat}
          lv.ar(lv.z(x, 0n, k), 0n, k, x, b, lv.L(lv.sl(ta, Nil{}, b)), 0n, lv.L(ta), Nat.mul(P, bo), lv.snd({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n), 10n) == True{} : Bool}, {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n), Nat.add(0n, k)) == Nat.add(x, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(x, Nat.add(0n, k))))) : Nat}, lv.snd({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n)) : Char}, ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n), Nat.add(0n, k)) == Nat.add(x, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(x, Nat.add(0n, k))))) : Nat}), LD.lv.t_sub(x, Nat.add(0n, k), hx, lv.yk(0n, k, {==}, hk)))), ih)
        case +y <> +tb:
          +hx = lv.and_l(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          +hta = lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          +hy = lv.and_l(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(tb), hb)
          +htb = lv.and_r(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(tb), hb)
          +b = Gt.sub.borrow(x, y, k)
          +P = lv.p10(List.length(&2, Nat, ta))
          +bo = lv.bo(ta, tb, b)
          +ih = lv.sub_value(ta, tb, b, hta, htb, lv.bw_le(Nat.is_lt(x, Nat.add(y, k))), hl)
          %Equal.sym(Nat, Nat.mul(Nat.mul(10n, P), bo), Nat.mul(10n, Nat.mul(P, bo)), LN.lv.mul_assoc(10n, P, bo)) : {Nat.add(lv.L(lv.sl(x <> ta, y <> tb, k)), Nat.add(lv.L(y <> tb), k)) == Nat.add(Nat.add(x, Nat.mul(10n, lv.L(ta))), _) : Nat}
          lv.ar(lv.z(x, y, k), y, k, x, b, lv.L(lv.sl(ta, tb, b)), lv.L(tb), lv.L(ta), Nat.mul(P, bo), lv.snd({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n), 10n) == True{} : Bool}, {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n), Nat.add(y, k)) == Nat.add(x, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(x, Nat.add(y, k))))) : Nat}, lv.snd({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n)) : Char}, ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n), Nat.add(y, k)) == Nat.add(x, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(x, Nat.add(y, k))))) : Nat}), LD.lv.t_sub(x, Nat.add(y, k), hx, lv.yk(y, k, hy, hk)))), ih)

# Bounds and the borrow
# ---------------------

def lv.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# the digits of the subtraction are digits
def lv.sl_digits(ra: List<&2, Nat>, rb: List<&2, Nat>, +k: Nat, +ha: {LawsBase.wire_digits_all(ra) == True{} : Bool}, +hb: {LawsBase.wire_digits_all(rb) == True{} : Bool}, +hk: {Nat.is_le(k, 1n) == True{} : Bool}) -> {LawsBase.wire_digits_all(lv.sl(ra, rb, k)) == True{} : Bool}:
  match ra:
    case Nil{}:
      {==}
    case +x <> +ta:
      match rb:
        case Nil{}:
          +hx = lv.and_l(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          +hta = lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          lv.and_tt(Nat.is_lt(lv.z(x, 0n, k), 10n), LawsBase.wire_digits_all(lv.sl(ta, Nil{}, Gt.sub.borrow(x, 0n, k))), lv.fst({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n), 10n) == True{} : Bool}, {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n), Nat.add(0n, k)) == Nat.add(x, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(x, Nat.add(0n, k))))) : Nat}, lv.snd({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n)) : Char}, ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(0n, k)), 10n), Nat.add(0n, k)) == Nat.add(x, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(x, Nat.add(0n, k))))) : Nat}), LD.lv.t_sub(x, Nat.add(0n, k), hx, lv.yk(0n, k, {==}, hk)))), lv.sl_digits(ta, Nil{}, Gt.sub.borrow(x, 0n, k), hta, {==}, lv.bw_le(Nat.is_lt(x, Nat.add(0n, k)))))
        case +y <> +tb:
          +hx = lv.and_l(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          +hta = lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(ta), ha)
          +hy = lv.and_l(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(tb), hb)
          +htb = lv.and_r(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(tb), hb)
          lv.and_tt(Nat.is_lt(lv.z(x, y, k), 10n), LawsBase.wire_digits_all(lv.sl(ta, tb, Gt.sub.borrow(x, y, k))), lv.fst({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n), 10n) == True{} : Bool}, {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n), Nat.add(y, k)) == Nat.add(x, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(x, Nat.add(y, k))))) : Nat}, lv.snd({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n)) : Char}, ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, x), Nat.add(y, k)), 10n), Nat.add(y, k)) == Nat.add(x, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(x, Nat.add(y, k))))) : Nat}), LD.lv.t_sub(x, Nat.add(y, k), hx, lv.yk(y, k, hy, hk)))), lv.sl_digits(ta, tb, Gt.sub.borrow(x, y, k), hta, htb, lv.bw_le(Nat.is_lt(x, Nat.add(y, k)))))

# the subtraction has as many digits as ra
def lv.sl_len(ra: List<&2, Nat>, rb: List<&2, Nat>, +k: Nat) -> {List.length(&2, Nat, lv.sl(ra, rb, k)) == List.length(&2, Nat, ra) : Nat}:
  match ra:
    case Nil{}:
      {==}
    case +x <> ta:
      match rb:
        case Nil{}:
          Equal.cong(Nat, Nat, w => 1n+w, List.length(&2, Nat, lv.sl(ta, Nil{}, Gt.sub.borrow(x, 0n, k))), List.length(&2, Nat, ta), lv.sl_len(ta, Nil{}, Gt.sub.borrow(x, 0n, k)))
        case +y <> tb:
          Equal.cong(Nat, Nat, w => 1n+w, List.length(&2, Nat, lv.sl(ta, tb, Gt.sub.borrow(x, y, k))), List.length(&2, Nat, ta), lv.sl_len(ta, tb, Gt.sub.borrow(x, y, k)))

def lv.Lb.step(+Lr: Nat, +P: Nat, ih: {Nat.is_le(1n+Lr, P) == True{} : Bool}) -> {Nat.is_le(Nat.add(10n, Nat.mul(10n, Lr)), Nat.mul(10n, P)) == True{} : Bool}:
  %LN.lv.mul_succ(10n, Lr) : {Nat.is_le(_, Nat.mul(10n, P)) == True{} : Bool}
  LN.lv.mul_le_r(10n, 1n+Lr, P, ih)

# digits least significant first are worth less than 10^n
def lv.L_bound(xs: List<&2, Nat>, +h: {LawsBase.wire_digits_all(xs) == True{} : Bool}) -> {Nat.is_le(1n+lv.L(xs), lv.p10(List.length(&2, Nat, xs))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      +hx = lv.and_l(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(r), h)
      +hr = lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(r), h)
      +M = Nat.mul(10n, lv.L(r))
      LN.lv.le_trans(1n+Nat.add(x, M), Nat.add(10n, M), Nat.mul(10n, lv.p10(List.length(&2, Nat, r))), LN.lv.add_le_r(1n+x, 10n, M, lv.lt_le(x, 9n, hx)), lv.Lb.step(lv.L(r), lv.p10(List.length(&2, Nat, r)), lv.L_bound(r, hr)))

# no borrow is left when the first is worth at least the second: the
# subtraction is then worth their difference
def lv.nob(+Lres: Nat, +LU: Nat, +LB: Nat, +P: Nat, bo: Nat, eq: {Nat.add(Lres, Nat.add(LU, 0n)) == Nat.add(LB, Nat.mul(P, bo)) : Nat}, hb: {Nat.is_le(1n+Lres, P) == True{} : Bool}, hu: {Nat.is_le(LU, LB) == True{} : Bool}, hbo: {Nat.is_le(bo, 1n) == True{} : Bool}) -> {Nat.sub(LB, LU) == Lres : Nat}:
  match bo:
    case 0n:
      LN.lv.sub_of(Lres, LU, LB, Equal.trans(Nat, Nat.add(Lres, LU), Nat.add(Lres, Nat.add(LU, 0n)), LB,
        Equal.cong(Nat, Nat, w => Nat.add(Lres, w), LU, Nat.add(LU, 0n), Equal.sym(Nat, Nat.add(LU, 0n), LU, LN.lv.add_zero(LU))),
        Equal.trans(Nat, Nat.add(Lres, Nat.add(LU, 0n)), Nat.add(LB, Nat.mul(P, 0n)), LB, eq,
          Equal.trans(Nat, Nat.add(LB, Nat.mul(P, 0n)), Nat.add(LB, 0n), LB, Equal.cong(Nat, Nat, w => Nat.add(LB, w), Nat.mul(P, 0n), 0n, LN.lv.mul_zero(P)), LN.lv.add_zero(LB)))))
    case 1n+j:
      match j:
        case 0n:
          +X = Nat.add(Lres, LU)
          +e1 = Equal.trans(Nat, X, Nat.add(Lres, Nat.add(LU, 0n)), Nat.add(LB, P),
            Equal.cong(Nat, Nat, w => Nat.add(Lres, w), LU, Nat.add(LU, 0n), Equal.sym(Nat, Nat.add(LU, 0n), LU, LN.lv.add_zero(LU))),
            Equal.trans(Nat, Nat.add(Lres, Nat.add(LU, 0n)), Nat.add(LB, Nat.mul(P, 1n)), Nat.add(LB, P), eq, Equal.cong(Nat, Nat, w => Nat.add(LB, w), Nat.mul(P, 1n), P, LN.lv.mul_one(P))))
          +le = LN.lv.add_le(1n+Lres, P, LU, LB, hb, hu)
          +e2 = Equal.trans(Nat, Nat.add(P, LB), Nat.add(LB, P), X, LN.lv.add_comm(P, LB), Equal.sym(Nat, X, Nat.add(LB, P), e1))
          +le2 = Equal.trans(Bool, Nat.is_le(1n+X, X), Nat.is_le(1n+X, Nat.add(P, LB)), True{}, Equal.cong(Nat, Bool, w => Nat.is_le(1n+X, w), X, Nat.add(P, LB), Equal.sym(Nat, Nat.add(P, LB), X, e2)), le)
          LN.lv.absurd({Nat.sub(LB, LU) == Lres : Nat}, Equal.trans(Bool, False{}, Nat.is_le(1n+X, X), True{}, Equal.sym(Bool, Nat.is_le(1n+X, X), False{}, LN.lv.succ_le_self(X)), le2))
        case 1n+i:
          LN.lv.absurd({Nat.sub(LB, LU) == Lres : Nat}, hbo)

# the borrow left is 0 or 1
def lv.bo_le(ra: List<&2, Nat>, rb: List<&2, Nat>, +k: Nat, hk: {Nat.is_le(k, 1n) == True{} : Bool}) -> {Nat.is_le(lv.bo(ra, rb, k), 1n) == True{} : Bool}:
  match ra:
    case Nil{}:
      hk
    case +x <> ta:
      match rb:
        case Nil{}:
          lv.bo_le(ta, Nil{}, Gt.sub.borrow(x, 0n, k), lv.bw_le(Nat.is_lt(x, Nat.add(0n, k))))
        case +y <> tb:
          lv.bo_le(ta, tb, Gt.sub.borrow(x, y, k), lv.bw_le(Nat.is_lt(x, Nat.add(y, k))))

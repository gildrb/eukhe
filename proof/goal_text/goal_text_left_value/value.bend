# eukhe: lemmas of LAW goal_text_left_value: values, reversal, canon, read
#
# Digits most significant first (gt_value) reversed (lv.lrev) are worth as
# digits least significant first (lv.L); the code's String.reverse and
# canon on digit chars are lv.lrev and lv.cn on the digits (lv.rev_D,
# lv.canon_D), canon keeps the value (lv.V_cn), and the spec reads digit
# chars back as their digits (lv.read_D).

import Base
import ../../../bend/goal_text.bend as Gt
import ../../../laws/base.bend as LawsBase
import ../../../laws/goal_text.bend as GoalText
import ./nat.bend as LN
import ./digits.bend as LD
import ./sub.bend as LS

# Reversal
# --------

def lv.lrev(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case x <> r:
      lv.lrev(r, x <> acc)

def lv.rev_D(xs: List<&2, Nat>, acc: List<&2, Nat>) -> {String.reverse.go(LawsBase.wire_digit_chars(xs, ""), LawsBase.wire_digit_chars(acc, "")) == LawsBase.wire_digit_chars(lv.lrev(xs, acc), "") : String}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      lv.rev_D(r, x <> acc)

def lv.LR(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {LS.lv.L(lv.lrev(xs, acc)) == GoalText.gt_value.go(xs, LS.lv.L(acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      +La = LS.lv.L(acc)
      Equal.trans(Nat, LS.lv.L(lv.lrev(r, x <> acc)), GoalText.gt_value.go(r, Nat.add(x, Nat.mul(10n, La))), GoalText.gt_value.go(r, Nat.add(Nat.mul(La, 10n), x)), lv.LR(r, x <> acc),
        Equal.cong(Nat, Nat, w => GoalText.gt_value.go(r, w), Nat.add(x, Nat.mul(10n, La)), Nat.add(Nat.mul(La, 10n), x),
          Equal.trans(Nat, Nat.add(x, Nat.mul(10n, La)), Nat.add(Nat.mul(10n, La), x), Nat.add(Nat.mul(La, 10n), x), LN.lv.add_comm(x, Nat.mul(10n, La)),
            Equal.cong(Nat, Nat, w => Nat.add(w, x), Nat.mul(10n, La), Nat.mul(La, 10n), LN.lv.mul_comm(10n, La)))))

def lv.app_nil(xs: List<&2, Nat>) -> {List.append(&2, Nat, xs, Nil{}) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, w => x <> w, List.append(&2, Nat, r, Nil{}), r, lv.app_nil(r))

def lv.rr(xs: List<&2, Nat>, acc: List<&2, Nat>, ys: List<&2, Nat>) -> {lv.lrev(lv.lrev(xs, acc), ys) == lv.lrev(acc, List.append(&2, Nat, xs, ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      lv.rr(r, x <> acc, ys)

def lv.rev_rev(+xs: List<&2, Nat>) -> {lv.lrev(lv.lrev(xs, Nil{}), Nil{}) == xs : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, lv.lrev(lv.lrev(xs, Nil{}), Nil{}), List.append(&2, Nat, xs, Nil{}), xs, lv.rr(xs, Nil{}, Nil{}), lv.app_nil(xs))

# reversed digits least significant first are worth the digits
def lv.L_rev(xs: List<&2, Nat>) -> {LS.lv.L(lv.lrev(xs, Nil{})) == GoalText.gt_value(xs) : Nat}:
  lv.LR(xs, Nil{})

# reversed digits are worth the digits least significant first
def lv.V_rev(+xs: List<&2, Nat>) -> {GoalText.gt_value(lv.lrev(xs, Nil{})) == LS.lv.L(xs) : Nat}:
  +ys = lv.lrev(xs, Nil{})
  Equal.trans(Nat, GoalText.gt_value(ys), LS.lv.L(lv.lrev(ys, Nil{})), LS.lv.L(xs), Equal.sym(Nat, LS.lv.L(lv.lrev(ys, Nil{})), GoalText.gt_value(ys), lv.LR(ys, Nil{})),
    Equal.cong(List<&2, Nat>, Nat, w => LS.lv.L(w), lv.lrev(ys, Nil{}), xs, lv.rev_rev(xs)))

def lv.rev_digits(xs: List<&2, Nat>, +acc: List<&2, Nat>, +hx: {LawsBase.wire_digits_all(xs) == True{} : Bool}, +ha: {LawsBase.wire_digits_all(acc) == True{} : Bool}) -> {LawsBase.wire_digits_all(lv.lrev(xs, acc)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case +x <> +r:
      lv.rev_digits(r, x <> acc, LS.lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(r), hx), LS.lv.and_tt(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(acc), LS.lv.and_l(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(r), hx), ha))

def lv.rev_len(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {List.length(&2, Nat, lv.lrev(xs, acc)) == Nat.add(List.length(&2, Nat, xs), List.length(&2, Nat, acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      Equal.trans(Nat, List.length(&2, Nat, lv.lrev(r, x <> acc)), Nat.add(List.length(&2, Nat, r), 1n+List.length(&2, Nat, acc)), 1n+Nat.add(List.length(&2, Nat, r), List.length(&2, Nat, acc)), lv.rev_len(r, x <> acc), LN.lv.add_succ(List.length(&2, Nat, r), List.length(&2, Nat, acc)))

def lv.rev_len0(+xs: List<&2, Nat>) -> {List.length(&2, Nat, lv.lrev(xs, Nil{})) == List.length(&2, Nat, xs) : Nat}:
  Equal.trans(Nat, List.length(&2, Nat, lv.lrev(xs, Nil{})), Nat.add(List.length(&2, Nat, xs), 0n), List.length(&2, Nat, xs), lv.rev_len(xs, Nil{}), LN.lv.add_zero(List.length(&2, Nat, xs)))

# Canon
# -----

def lv.strip.at(b: Bool, +x: Nat, r: List<&2, Nat>, s: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      s
    case False{}:
      x <> r

# the digits without their leading zeros
def lv.strip(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +r:
      lv.strip.at(Nat.is_eq(x, 0n), x, r, lv.strip(r))

def lv.fin(ys: List<&2, Nat>) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      [0n]
    case y <> w:
      y <> w

def lv.cn(xs: List<&2, Nat>) -> List<&2, Nat>:
  lv.fin(lv.strip(xs))

def lv.canon_at(b: Bool, +x: Nat, +r: List<&2, Nat>, s: List<&2, Nat>) -> {Gt.canon.at(b, LawsBase.wire_dec_char(x), LawsBase.wire_digit_chars(r, ""), LawsBase.wire_digit_chars(s, "")) == LawsBase.wire_digit_chars(lv.strip.at(b, x, r, s), "") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def lv.canon_go(xs: List<&2, Nat>, +h: {LawsBase.wire_digits_all(xs) == True{} : Bool}) -> {Gt.canon.go(LawsBase.wire_digit_chars(xs, "")) == LawsBase.wire_digit_chars(lv.strip(xs), "") : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      +hx = LS.lv.and_l(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(r), h)
      +hr = LS.lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(r), h)
      +Dr = LawsBase.wire_digit_chars(r, "")
      %Equal.sym(Bool, Char.is_eq(LawsBase.wire_dec_char(x), '0'), Nat.is_eq(x, 0n), LD.lv.t_zero(x, hx)) : {Gt.canon.at(_, LawsBase.wire_dec_char(x), Dr, Gt.canon.go(Dr)) == LawsBase.wire_digit_chars(lv.strip(x <> r), "") : String}
      %Equal.sym(String, Gt.canon.go(Dr), LawsBase.wire_digit_chars(lv.strip(r), ""), lv.canon_go(r, hr)) : {Gt.canon.at(Nat.is_eq(x, 0n), LawsBase.wire_dec_char(x), Dr, _) == LawsBase.wire_digit_chars(lv.strip(x <> r), "") : String}
      lv.canon_at(Nat.is_eq(x, 0n), x, r, lv.strip(r))

def lv.canon_fin(ys: List<&2, Nat>) -> {Gt.canon.fin(LawsBase.wire_digit_chars(ys, "")) == LawsBase.wire_digit_chars(lv.fin(ys), "") : String}:
  match ys:
    case Nil{}:
      {==}
    case y <> w:
      {==}

def lv.canon_D(+xs: List<&2, Nat>, h: {LawsBase.wire_digits_all(xs) == True{} : Bool}) -> {Gt.canon(LawsBase.wire_digit_chars(xs, "")) == LawsBase.wire_digit_chars(lv.cn(xs), "") : String}:
  %Equal.sym(String, Gt.canon.go(LawsBase.wire_digit_chars(xs, "")), LawsBase.wire_digit_chars(lv.strip(xs), ""), lv.canon_go(xs, h)) : {Gt.canon.fin(_) == LawsBase.wire_digit_chars(lv.cn(xs), "") : String}
  lv.canon_fin(lv.strip(xs))

def lv.V_strip(xs: List<&2, Nat>) -> {GoalText.gt_value(lv.strip(xs)) == GoalText.gt_value(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      match x:
        case 0n:
          lv.V_strip(r)
        case 1n+p:
          {==}

def lv.V_fin(ys: List<&2, Nat>) -> {GoalText.gt_value(lv.fin(ys)) == GoalText.gt_value(ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case y <> w:
      {==}

def lv.V_cn(+xs: List<&2, Nat>) -> {GoalText.gt_value(lv.cn(xs)) == GoalText.gt_value(xs) : Nat}:
  Equal.trans(Nat, GoalText.gt_value(lv.cn(xs)), GoalText.gt_value(lv.strip(xs)), GoalText.gt_value(xs), lv.V_fin(lv.strip(xs)), lv.V_strip(xs))

def lv.strip_digits(xs: List<&2, Nat>, h: {LawsBase.wire_digits_all(xs) == True{} : Bool}) -> {LawsBase.wire_digits_all(lv.strip(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      match x:
        case 0n:
          lv.strip_digits(r, h)
        case 1n+p:
          h

def lv.fin_digits(ys: List<&2, Nat>, h: {LawsBase.wire_digits_all(ys) == True{} : Bool}) -> {LawsBase.wire_digits_all(lv.fin(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case y <> w:
      h

def lv.cn_digits(+xs: List<&2, Nat>, h: {LawsBase.wire_digits_all(xs) == True{} : Bool}) -> {LawsBase.wire_digits_all(lv.cn(xs)) == True{} : Bool}:
  lv.fin_digits(lv.strip(xs), lv.strip_digits(xs, h))

# canonical digits: one digit, or a first digit that is not 0
def lv.ok(ys: List<&2, Nat>) -> Bool:
  match ys:
    case Nil{}:
      False{}
    case y <> w:
      match w:
        case Nil{}:
          True{}
        case z <> v:
          Bool.not(Nat.is_eq(y, 0n))

# no digits, or a first digit that is not 0
def lv.sok(ys: List<&2, Nat>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case y <> w:
      Bool.not(Nat.is_eq(y, 0n))

def lv.strip_sok(xs: List<&2, Nat>) -> {lv.sok(lv.strip(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      match x:
        case 0n:
          lv.strip_sok(r)
        case 1n+p:
          {==}

def lv.fin_ok(ys: List<&2, Nat>, h: {lv.sok(ys) == True{} : Bool}) -> {lv.ok(lv.fin(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case y <> w:
      match w:
        case Nil{}:
          {==}
        case z <> v:
          h

def lv.cn_ok(+xs: List<&2, Nat>) -> {lv.ok(lv.cn(xs)) == True{} : Bool}:
  lv.fin_ok(lv.strip(xs), lv.strip_sok(xs))

# Read
# ----

def lv.digits_D(ys: List<&2, Nat>, +h: {LawsBase.wire_digits_all(ys) == True{} : Bool}) -> {GoalText.gt_digits(LawsBase.wire_digit_chars(ys, "")) == Some{ys} : Maybe<&2, List<&2, Nat>>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +w:
      +hy = LS.lv.and_l(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(w), h)
      +hw = LS.lv.and_r(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(w), h)
      +Dw = LawsBase.wire_digit_chars(w, "")
      %Equal.sym(Maybe<&2, List<&2, Nat>>, GoalText.gt_digits(SCon{LawsBase.wire_dec_char(y), Dw}), GoalText.gt_digits.put(y, GoalText.gt_digits(Dw)), LD.lv.t_read(y, Dw, hy)) : {_ == Some{y <> w} : Maybe<&2, List<&2, Nat>>}
      %Equal.sym(Maybe<&2, List<&2, Nat>>, GoalText.gt_digits(Dw), Some{w}, lv.digits_D(w, hw)) : {GoalText.gt_digits.put(y, _) == Some{y <> w} : Maybe<&2, List<&2, Nat>>}
      {==}

# digit chars, at least one, read back as their value
def lv.read_D(ys: List<&2, Nat>, h: {LawsBase.wire_digits_all(ys) == True{} : Bool}, ne: {lv.ok(ys) == True{} : Bool}) -> {GoalText.gt_read(LawsBase.wire_digit_chars(ys, "")) == Some{GoalText.gt_value(ys)} : Maybe<&2, Nat>}:
  match ys:
    case Nil{}:
      LN.lv.absurd({GoalText.gt_read(LawsBase.wire_digit_chars(Nil{}, "")) == Some{GoalText.gt_value(Nil{})} : Maybe<&2, Nat>}, ne)
    case +y <> +w:
      %Equal.sym(Maybe<&2, List<&2, Nat>>, GoalText.gt_digits(LawsBase.wire_digit_chars(y <> w, "")), Some{y <> w}, lv.digits_D(y <> w, h)) : {GoalText.gt_read.of(_) == Some{GoalText.gt_value(y <> w)} : Maybe<&2, Nat>}
      {==}

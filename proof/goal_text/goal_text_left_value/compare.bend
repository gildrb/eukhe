# eukhe: lemmas of LAW goal_text_left_value: the comparison
#
# The code's `below` on digit chars reads their lengths and their order
# char by char (String.order); on digits that is lv.below (lv.below_D).
# For canonical digits (lv.ok) it answers by the values: true only when
# the first is worth at most the second (lv.below_true), false only when
# the second is worth at most the first and has no more digits
# (lv.below_false). A first digit d of n more is worth d * 10^n at least
# and with the rest less than (d + 1) * 10^n (lv.V_cons, lv.V_bound).

import Base
import ../../../bend/goal_text.bend as Gt
import ../../../laws/base.bend as LawsBase
import ../../../laws/goal_text.bend as GoalText
import ./nat.bend as LN
import ./digits.bend as LD
import ./sub.bend as LS
import ./value.bend as LV

# the order of two digit lists, item by item, after the order c of the
# items before (String.order.go on their chars)
def lv.ord(a: List<&2, Nat>, b: List<&2, Nat>, c: Cmp) -> Cmp:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          c
        case y <> t2:
          match c:
            case LT{}:
              LT{}
            case GT{}:
              GT{}
            case EQ{}:
              LT{}
    case +x <> t1:
      match b:
        case Nil{}:
          match c:
            case LT{}:
              LT{}
            case GT{}:
              GT{}
            case EQ{}:
              GT{}
        case +y <> t2:
          match c:
            case LT{}:
              LT{}
            case GT{}:
              GT{}
            case EQ{}:
              lv.ord(t1, t2, Nat.cmp(x, y))

# once the items before differ, the order is theirs
def lv.ord_lt(a: List<&2, Nat>, b: List<&2, Nat>) -> {lv.ord(a, b, LT{}) == LT{} : Cmp}:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case y <> t:
          {==}
    case x <> t:
      match b:
        case Nil{}:
          {==}
        case y <> u:
          {==}

def lv.ord_gt(a: List<&2, Nat>, b: List<&2, Nat>) -> {lv.ord(a, b, GT{}) == GT{} : Cmp}:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case y <> t:
          {==}
    case x <> t:
      match b:
        case Nil{}:
          {==}
        case y <> u:
          {==}

def lv.order_D(xs: List<&2, Nat>, ys: List<&2, Nat>, c: Cmp, +hx: {LawsBase.wire_digits_all(xs) == True{} : Bool}, +hy: {LawsBase.wire_digits_all(ys) == True{} : Bool}) -> {String.order.go(LawsBase.wire_digit_chars(xs, ""), LawsBase.wire_digit_chars(ys, ""), c) == lv.ord(xs, ys, c) : Cmp}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          match c:
            case LT{}:
              {==}
            case GT{}:
              {==}
            case EQ{}:
              {==}
        case y <> t2:
          match c:
            case LT{}:
              {==}
            case GT{}:
              {==}
            case EQ{}:
              {==}
    case +x <> +t1:
      match ys:
        case Nil{}:
          match c:
            case LT{}:
              {==}
            case GT{}:
              {==}
            case EQ{}:
              {==}
        case +y <> +t2:
          match c:
            case LT{}:
              {==}
            case GT{}:
              {==}
            case EQ{}:
              +ex = LS.lv.and_l(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(t1), hx)
              +et = LS.lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(t1), hx)
              +ey = LS.lv.and_l(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(t2), hy)
              +eu = LS.lv.and_r(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(t2), hy)
              %Equal.sym(Cmp, U32.cmp(U32.from_nat(Nat.add(48n, x)), U32.from_nat(Nat.add(48n, y))), Nat.cmp(x, y), LD.lv.t_cmp(x, y, ex, ey)) : {String.order.go(LawsBase.wire_digit_chars(t1, ""), LawsBase.wire_digit_chars(t2, ""), _) == lv.ord(x <> t1, y <> t2, EQ{}) : Cmp}
              lv.order_D(t1, t2, Nat.cmp(x, y), et, eu)

def lv.len_D(xs: List<&2, Nat>) -> {String.length(LawsBase.wire_digit_chars(xs, "")) == List.length(&2, Nat, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      Equal.cong(Nat, Nat, w => 1n+w, String.length(LawsBase.wire_digit_chars(r, "")), List.length(&2, Nat, r), lv.len_D(r))

# B below U: fewer digits, or as many and before in order
def lv.below(+B: List<&2, Nat>, +U: List<&2, Nat>) -> Bool:
  +lb = List.length(&2, Nat, B)
  +lu = List.length(&2, Nat, U)
  Bool.or(Nat.is_lt(lb, lu), Bool.and(Nat.is_eq(lb, lu), Cmp.is_lt(lv.ord(B, U, EQ{}))))

def lv.below_D(+B: List<&2, Nat>, +U: List<&2, Nat>, hB: {LawsBase.wire_digits_all(B) == True{} : Bool}, hU: {LawsBase.wire_digits_all(U) == True{} : Bool}) -> {Gt.below(LawsBase.wire_digit_chars(B, ""), LawsBase.wire_digit_chars(U, "")) == lv.below(B, U) : Bool}:
  +DB = LawsBase.wire_digit_chars(B, "")
  +DU = LawsBase.wire_digit_chars(U, "")
  +lb = List.length(&2, Nat, B)
  +lu = List.length(&2, Nat, U)
  %Equal.sym(Nat, String.length(DB), lb, lv.len_D(B)) : {Bool.or(Nat.is_lt(_, String.length(DU)), Bool.and(Nat.is_eq(_, String.length(DU)), String.is_lt(DB, DU))) == lv.below(B, U) : Bool}
  %Equal.sym(Nat, String.length(DU), lu, lv.len_D(U)) : {Bool.or(Nat.is_lt(lb, _), Bool.and(Nat.is_eq(lb, _), String.is_lt(DB, DU))) == lv.below(B, U) : Bool}
  %Equal.sym(Cmp, String.order.go(DB, DU, EQ{}), lv.ord(B, U, EQ{}), lv.order_D(B, U, EQ{}, hB, hU)) : {Bool.or(Nat.is_lt(lb, lu), Bool.and(Nat.is_eq(lb, lu), Cmp.is_lt(_))) == lv.below(B, U) : Bool}
  {==}

# Values
# ------

def lv.V_go(xs: List<&2, Nat>, +a: Nat) -> {GoalText.gt_value.go(xs, a) == Nat.add(Nat.mul(a, LS.lv.p10(List.length(&2, Nat, xs))), GoalText.gt_value(xs)) : Nat}:
  match xs:
    case Nil{}:
      Equal.trans(Nat, a, Nat.mul(a, 1n), Nat.add(Nat.mul(a, 1n), 0n), Equal.sym(Nat, Nat.mul(a, 1n), a, LN.lv.mul_one(a)), Equal.sym(Nat, Nat.add(Nat.mul(a, 1n), 0n), Nat.mul(a, 1n), LN.lv.add_zero(Nat.mul(a, 1n))))
    case +x <> +r:
      +P = LS.lv.p10(List.length(&2, Nat, r))
      +Vr = GoalText.gt_value(r)
      +a1 = Nat.add(Nat.mul(a, 10n), x)
      Equal.trans(Nat, GoalText.gt_value.go(r, a1), Nat.add(Nat.mul(a1, P), Vr), Nat.add(Nat.mul(a, Nat.mul(10n, P)), GoalText.gt_value.go(r, x)), lv.V_go(r, a1),
        Equal.trans(Nat, Nat.add(Nat.mul(a1, P), Vr), Nat.add(Nat.add(Nat.mul(Nat.mul(a, 10n), P), Nat.mul(x, P)), Vr), Nat.add(Nat.mul(a, Nat.mul(10n, P)), GoalText.gt_value.go(r, x)),
          Equal.cong(Nat, Nat, w => Nat.add(w, Vr), Nat.mul(a1, P), Nat.add(Nat.mul(Nat.mul(a, 10n), P), Nat.mul(x, P)), LN.lv.mul_dist_r(Nat.mul(a, 10n), x, P)),
          Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(a, 10n), P), Nat.mul(x, P)), Vr), Nat.add(Nat.add(Nat.mul(a, Nat.mul(10n, P)), Nat.mul(x, P)), Vr), Nat.add(Nat.mul(a, Nat.mul(10n, P)), GoalText.gt_value.go(r, x)),
            Equal.cong(Nat, Nat, w => Nat.add(Nat.add(w, Nat.mul(x, P)), Vr), Nat.mul(Nat.mul(a, 10n), P), Nat.mul(a, Nat.mul(10n, P)), LN.lv.mul_assoc(a, 10n, P)),
            Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(a, Nat.mul(10n, P)), Nat.mul(x, P)), Vr), Nat.add(Nat.mul(a, Nat.mul(10n, P)), Nat.add(Nat.mul(x, P), Vr)), Nat.add(Nat.mul(a, Nat.mul(10n, P)), GoalText.gt_value.go(r, x)),
              LN.lv.add_assoc(Nat.mul(a, Nat.mul(10n, P)), Nat.mul(x, P), Vr),
              Equal.cong(Nat, Nat, w => Nat.add(Nat.mul(a, Nat.mul(10n, P)), w), Nat.add(Nat.mul(x, P), Vr), GoalText.gt_value.go(r, x), Equal.sym(Nat, GoalText.gt_value.go(r, x), Nat.add(Nat.mul(x, P), Vr), lv.V_go(r, x)))))))

# a first digit x of the digits r more is worth x * 10^n
def lv.V_cons(x: Nat, r: List<&2, Nat>) -> {GoalText.gt_value(x <> r) == Nat.add(Nat.mul(x, LS.lv.p10(List.length(&2, Nat, r))), GoalText.gt_value(r)) : Nat}:
  lv.V_go(r, x)

# digits are worth less than 10^n
def lv.V_bound(+xs: List<&2, Nat>, h: {LawsBase.wire_digits_all(xs) == True{} : Bool}) -> {Nat.is_le(1n+GoalText.gt_value(xs), LS.lv.p10(List.length(&2, Nat, xs))) == True{} : Bool}:
  +ys = LV.lv.lrev(xs, Nil{})
  %LV.lv.L_rev(xs) : {Nat.is_le(1n+_, LS.lv.p10(List.length(&2, Nat, xs))) == True{} : Bool}
  %LV.lv.rev_len0(xs) : {Nat.is_le(1n+LS.lv.L(ys), LS.lv.p10(_)) == True{} : Bool}
  LS.lv.L_bound(ys, LV.lv.rev_digits(xs, Nil{}, h, {==}))

def lv.le_succ_r(a: Nat) -> {Nat.is_le(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      lv.le_succ_r(p)

def lv.le_of_succ(+a: Nat, b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  LN.lv.le_trans(a, 1n+a, b, lv.le_succ_r(a), h)

def lv.p10_pos(n: Nat) -> {Nat.is_le(1n, LS.lv.p10(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      LN.lv.le_trans(1n, 10n, Nat.mul(10n, LS.lv.p10(m)), {==}, LN.lv.mul_le_r(10n, 1n, LS.lv.p10(m), lv.p10_pos(m)))

def lv.p10_mono(m: Nat, n: Nat, h: {Nat.is_le(m, n) == True{} : Bool}) -> {Nat.is_le(LS.lv.p10(m), LS.lv.p10(n)) == True{} : Bool}:
  match m:
    case 0n:
      lv.p10_pos(n)
    case 1n++i:
      match n:
        case 0n:
          LN.lv.absurd({Nat.is_le(LS.lv.p10(1n+i), LS.lv.p10(0n)) == True{} : Bool}, h)
        case 1n++j:
          LN.lv.mul_le_r(10n, LS.lv.p10(i), LS.lv.p10(j), lv.p10_mono(i, j, h))

# a first digit that is not 0, of n more: worth 10^n at least
def lv.V_lower(u: Nat, +w: List<&2, Nat>, hu: {Nat.is_eq(u, 0n) == False{} : Bool}) -> {Nat.is_le(LS.lv.p10(List.length(&2, Nat, w)), GoalText.gt_value(u <> w)) == True{} : Bool}:
  match u:
    case 0n:
      LN.lv.absurd({Nat.is_le(LS.lv.p10(List.length(&2, Nat, w)), GoalText.gt_value(0n <> w)) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, hu))
    case 1n++v:
      +P = LS.lv.p10(List.length(&2, Nat, w))
      +Vw = GoalText.gt_value(w)
      %Equal.sym(Nat, GoalText.gt_value((1n+v) <> w), Nat.add(Nat.mul(1n+v, P), Vw), lv.V_cons(1n+v, w)) : {Nat.is_le(P, _) == True{} : Bool}
      LN.lv.le_trans(P, Nat.add(P, Nat.mul(v, P)), Nat.add(Nat.add(P, Nat.mul(v, P)), Vw), LN.lv.le_add(P, Nat.mul(v, P)), LN.lv.le_add(Nat.add(P, Nat.mul(v, P)), Vw))

# Comparisons
# -----------

def lv.CEq(c: Cmp, G: Type) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      G
    case GT{}:
      Unit

def lv.CGt(c: Cmp, G: Type) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Unit
    case GT{}:
      G

def lv.ne_eq(-G: Type, -c: Cmp, e: {c == EQ{} : Cmp}, n: lv.CEq(c, G)) -> G:
  %e : lv.CEq(_, G)
  n

def lv.ne_gt(-G: Type, -c: Cmp, e: {c == GT{} : Cmp}, n: lv.CGt(c, G)) -> G:
  %e : lv.CGt(_, G)
  n

def lv.eq_of(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          LN.lv.absurd({0n == 1n+q : Nat}, h)
    case 1n+p:
      match b:
        case 0n:
          LN.lv.absurd({1n+p == 0n : Nat}, h)
        case 1n+q:
          Equal.cong(Nat, Nat, w => 1n+w, p, q, lv.eq_of(p, q, h))

def lv.cmp_eq(x: Nat, y: Nat, e: {Nat.cmp(x, y) == EQ{} : Cmp}) -> {x == y : Nat}:
  match x:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n+q:
          lv.ne_eq({0n == 1n+q : Nat}, LT{}, e, Unit{})
    case 1n+p:
      match y:
        case 0n:
          lv.ne_eq({1n+p == 0n : Nat}, GT{}, e, Unit{})
        case 1n+q:
          Equal.cong(Nat, Nat, w => 1n+w, p, q, lv.cmp_eq(p, q, e))

def lv.cmp_lt(x: Nat, y: Nat, e: {Nat.cmp(x, y) == LT{} : Cmp}) -> {Nat.is_le(1n+x, y) == True{} : Bool}:
  match x:
    case 0n:
      match y:
        case 0n:
          lv.ne_eq({Nat.is_le(1n, 0n) == True{} : Bool}, LT{}, Equal.sym(Cmp, EQ{}, LT{}, e), Unit{})
        case 1n+q:
          LN.lv.le_zero(q)
    case 1n+p:
      match y:
        case 0n:
          lv.ne_gt({Nat.is_le(2n+p, 0n) == True{} : Bool}, LT{}, Equal.sym(Cmp, GT{}, LT{}, e), Unit{})
        case 1n+q:
          lv.cmp_lt(p, q, e)

def lv.cmp_gt(x: Nat, y: Nat, e: {Nat.cmp(x, y) == GT{} : Cmp}) -> {Nat.is_le(1n+y, x) == True{} : Bool}:
  match x:
    case 0n:
      match y:
        case 0n:
          lv.ne_gt({Nat.is_le(1n, 0n) == True{} : Bool}, EQ{}, e, Unit{})
        case 1n+q:
          lv.ne_gt({Nat.is_le(2n+q, 0n) == True{} : Bool}, LT{}, e, Unit{})
    case 1n+p:
      match y:
        case 0n:
          LN.lv.le_zero(p)
        case 1n+q:
          lv.cmp_gt(p, q, e)

def lv.lt_val.tail(+x: Nat, +y: Nat, +P: Nat, +Vv: Nat, hxy: {Nat.is_le(1n+x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.mul(x, P), P), Nat.add(Nat.mul(y, P), Vv)) == True{} : Bool}:
  %LN.lv.add_comm(P, Nat.mul(x, P)) : {Nat.is_le(_, Nat.add(Nat.mul(y, P), Vv)) == True{} : Bool}
  LN.lv.le_trans(Nat.mul(1n+x, P), Nat.mul(y, P), Nat.add(Nat.mul(y, P), Vv), LN.lv.mul_le_l(1n+x, y, P, hxy), LN.lv.le_add(Nat.mul(y, P), Vv))

# a smaller first digit, as many after it: worth at most the other
def lv.lt_val(+x: Nat, +u: List<&2, Nat>, +y: Nat, +v: List<&2, Nat>, hl: {List.length(&2, Nat, u) == List.length(&2, Nat, v) : Nat}, hu: {LawsBase.wire_digits_all(u) == True{} : Bool}, hxy: {Nat.is_le(1n+x, y) == True{} : Bool}) -> {Nat.is_le(GoalText.gt_value(x <> u), GoalText.gt_value(y <> v)) == True{} : Bool}:
  +P = LS.lv.p10(List.length(&2, Nat, u))
  +Vu = GoalText.gt_value(u)
  +Vv = GoalText.gt_value(v)
  %Equal.sym(Nat, GoalText.gt_value(x <> u), Nat.add(Nat.mul(x, P), Vu), lv.V_cons(x, u)) : {Nat.is_le(_, GoalText.gt_value(y <> v)) == True{} : Bool}
  %Equal.sym(Nat, GoalText.gt_value(y <> v), Nat.add(Nat.mul(y, LS.lv.p10(List.length(&2, Nat, v))), Vv), lv.V_cons(y, v)) : {Nat.is_le(Nat.add(Nat.mul(x, P), Vu), _) == True{} : Bool}
  %hl : {Nat.is_le(Nat.add(Nat.mul(x, P), Vu), Nat.add(Nat.mul(y, LS.lv.p10(_)), Vv)) == True{} : Bool}
  LN.lv.le_trans(Nat.add(Nat.mul(x, P), Vu), Nat.add(Nat.mul(x, P), P), Nat.add(Nat.mul(y, P), Vv), LN.lv.add_le_l(Nat.mul(x, P), Vu, P, lv.le_of_succ(Vu, P, lv.V_bound(u, hu))), lv.lt_val.tail(x, y, P, Vv, hxy))

# the same first digit: compare the rest
def lv.eq_val(+x: Nat, +u: List<&2, Nat>, +v: List<&2, Nat>, hl: {List.length(&2, Nat, u) == List.length(&2, Nat, v) : Nat}, h: {Nat.is_le(GoalText.gt_value(u), GoalText.gt_value(v)) == True{} : Bool}) -> {Nat.is_le(GoalText.gt_value(x <> u), GoalText.gt_value(x <> v)) == True{} : Bool}:
  +P = LS.lv.p10(List.length(&2, Nat, u))
  %Equal.sym(Nat, GoalText.gt_value(x <> u), Nat.add(Nat.mul(x, P), GoalText.gt_value(u)), lv.V_cons(x, u)) : {Nat.is_le(_, GoalText.gt_value(x <> v)) == True{} : Bool}
  %Equal.sym(Nat, GoalText.gt_value(x <> v), Nat.add(Nat.mul(x, LS.lv.p10(List.length(&2, Nat, v))), GoalText.gt_value(v)), lv.V_cons(x, v)) : {Nat.is_le(Nat.add(Nat.mul(x, P), GoalText.gt_value(u)), _) == True{} : Bool}
  %hl : {Nat.is_le(Nat.add(Nat.mul(x, P), GoalText.gt_value(u)), Nat.add(Nat.mul(x, LS.lv.p10(_)), GoalText.gt_value(v))) == True{} : Bool}
  LN.lv.add_le_l(Nat.mul(x, P), GoalText.gt_value(u), GoalText.gt_value(v), h)

# order lemmas on Nat
def lv.lt_succ_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          LN.lv.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, h)
        case 1n+q:
          LN.lv.le_zero(q)
    case 1n+p:
      match b:
        case 0n:
          LN.lv.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, h)
        case 1n+q:
          lv.lt_succ_le(p, q, h)

def lv.nlt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          LN.lv.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case 1n+p:
      match b:
        case 0n:
          {==}
        case 1n+q:
          lv.nlt_le(p, q, h)

def lv.le_ne(a: Nat, b: Nat, le: {Nat.is_le(a, b) == True{} : Bool}, ne: {Nat.is_eq(b, a) == False{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          LN.lv.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, ne))
        case 1n+q:
          LN.lv.le_zero(q)
    case 1n+p:
      match b:
        case 0n:
          LN.lv.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, le)
        case 1n+q:
          lv.le_ne(p, q, le, ne)

def lv.not_true(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LN.lv.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def lv.ok_len(B: List<&2, Nat>, ok: {LV.lv.ok(B) == True{} : Bool}) -> {Nat.is_le(1n, List.length(&2, Nat, B)) == True{} : Bool}:
  match B:
    case Nil{}:
      LN.lv.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, ok)
    case b <> t:
      LN.lv.le_zero(List.length(&2, Nat, t))

# Lexical order of digits of one length
# -------------------------------------

def lv.lex_lt.at(+x: Nat, +u: List<&2, Nat>, +y: Nat, +v: List<&2, Nat>, c: Cmp, ec: {Nat.cmp(x, y) == c : Cmp}, +hl: {Nat.is_eq(List.length(&2, Nat, u), List.length(&2, Nat, v)) == True{} : Bool}, +hu: {LawsBase.wire_digits_all(u) == True{} : Bool}, h: {Cmp.is_lt(lv.ord(u, v, c)) == True{} : Bool}, ih: {Cmp.is_lt(lv.ord(u, v, EQ{})) == True{} : Bool} -> {Nat.is_le(GoalText.gt_value(u), GoalText.gt_value(v)) == True{} : Bool}) -> {Nat.is_le(GoalText.gt_value(x <> u), GoalText.gt_value(y <> v)) == True{} : Bool}:
  match c:
    case LT{}:
      lv.lt_val(x, u, y, v, lv.eq_of(List.length(&2, Nat, u), List.length(&2, Nat, v), hl), hu, lv.cmp_lt(x, y, ec))
    case EQ{}:
      %lv.cmp_eq(x, y, ec) : {Nat.is_le(GoalText.gt_value(x <> u), GoalText.gt_value(_ <> v)) == True{} : Bool}
      lv.eq_val(x, u, v, lv.eq_of(List.length(&2, Nat, u), List.length(&2, Nat, v), hl), ih(h))
    case GT{}:
      LN.lv.absurd({Nat.is_le(GoalText.gt_value(x <> u), GoalText.gt_value(y <> v)) == True{} : Bool}, Equal.trans(Bool, False{}, Cmp.is_lt(lv.ord(u, v, GT{})), True{}, Equal.cong(Cmp, Bool, w => Cmp.is_lt(w), GT{}, lv.ord(u, v, GT{}), Equal.sym(Cmp, lv.ord(u, v, GT{}), GT{}, lv.ord_gt(u, v))), h))

# digits of one length before in order are worth at most the others
def lv.lex_lt(xs: List<&2, Nat>, ys: List<&2, Nat>, +hl: {Nat.is_eq(List.length(&2, Nat, xs), List.length(&2, Nat, ys)) == True{} : Bool}, hx: {LawsBase.wire_digits_all(xs) == True{} : Bool}, hy: {LawsBase.wire_digits_all(ys) == True{} : Bool}, h: {Cmp.is_lt(lv.ord(xs, ys, EQ{})) == True{} : Bool}) -> {Nat.is_le(GoalText.gt_value(xs), GoalText.gt_value(ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          LN.lv.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, h)
        case y <> v:
          LN.lv.absurd({Nat.is_le(0n, GoalText.gt_value(y <> v)) == True{} : Bool}, hl)
    case +x <> +u:
      match ys:
        case Nil{}:
          LN.lv.absurd({Nat.is_le(GoalText.gt_value(x <> u), 0n) == True{} : Bool}, hl)
        case +y <> +v:
          +hu = LS.lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(u), hx)
          +hv = LS.lv.and_r(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(v), hy)
          lv.lex_lt.at(x, u, y, v, Nat.cmp(x, y), {==}, hl, hu, h, h2 => lv.lex_lt(u, v, hl, hu, hv, h2))

def lv.lex_ge.at(+x: Nat, +u: List<&2, Nat>, +y: Nat, +v: List<&2, Nat>, c: Cmp, ec: {Nat.cmp(x, y) == c : Cmp}, +hl: {Nat.is_eq(List.length(&2, Nat, u), List.length(&2, Nat, v)) == True{} : Bool}, +hv: {LawsBase.wire_digits_all(v) == True{} : Bool}, h: {Cmp.is_lt(lv.ord(u, v, c)) == False{} : Bool}, ih: {Cmp.is_lt(lv.ord(u, v, EQ{})) == False{} : Bool} -> {Nat.is_le(GoalText.gt_value(v), GoalText.gt_value(u)) == True{} : Bool}) -> {Nat.is_le(GoalText.gt_value(y <> v), GoalText.gt_value(x <> u)) == True{} : Bool}:
  match c:
    case LT{}:
      LN.lv.absurd({Nat.is_le(GoalText.gt_value(y <> v), GoalText.gt_value(x <> u)) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, Equal.trans(Bool, True{}, Cmp.is_lt(lv.ord(u, v, LT{})), False{}, Equal.cong(Cmp, Bool, w => Cmp.is_lt(w), LT{}, lv.ord(u, v, LT{}), Equal.sym(Cmp, lv.ord(u, v, LT{}), LT{}, lv.ord_lt(u, v))), h)))
    case EQ{}:
      %lv.cmp_eq(x, y, ec) : {Nat.is_le(GoalText.gt_value(_ <> v), GoalText.gt_value(x <> u)) == True{} : Bool}
      lv.eq_val(x, v, u, Equal.sym(Nat, List.length(&2, Nat, u), List.length(&2, Nat, v), lv.eq_of(List.length(&2, Nat, u), List.length(&2, Nat, v), hl)), ih(h))
    case GT{}:
      lv.lt_val(y, v, x, u, Equal.sym(Nat, List.length(&2, Nat, u), List.length(&2, Nat, v), lv.eq_of(List.length(&2, Nat, u), List.length(&2, Nat, v), hl)), hv, lv.cmp_gt(x, y, ec))

# digits of one length not before in order are worth at least the others
def lv.lex_ge(xs: List<&2, Nat>, ys: List<&2, Nat>, +hl: {Nat.is_eq(List.length(&2, Nat, xs), List.length(&2, Nat, ys)) == True{} : Bool}, hx: {LawsBase.wire_digits_all(xs) == True{} : Bool}, hy: {LawsBase.wire_digits_all(ys) == True{} : Bool}, h: {Cmp.is_lt(lv.ord(xs, ys, EQ{})) == False{} : Bool}) -> {Nat.is_le(GoalText.gt_value(ys), GoalText.gt_value(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case y <> v:
          LN.lv.absurd({Nat.is_le(GoalText.gt_value(y <> v), 0n) == True{} : Bool}, hl)
    case +x <> +u:
      match ys:
        case Nil{}:
          LN.lv.absurd({Nat.is_le(0n, GoalText.gt_value(x <> u)) == True{} : Bool}, hl)
        case +y <> +v:
          +hu = LS.lv.and_r(Nat.is_lt(x, 10n), LawsBase.wire_digits_all(u), hx)
          +hv = LS.lv.and_r(Nat.is_lt(y, 10n), LawsBase.wire_digits_all(v), hy)
          lv.lex_ge.at(x, u, y, v, Nat.cmp(x, y), {==}, hl, hv, h, h2 => lv.lex_ge(u, v, hl, hu, hv, h2))

# Fewer digits
# ------------

# canonical digits with more digits are worth at least
def lv.len_lt(+B: List<&2, Nat>, U: List<&2, Nat>, hB: {LawsBase.wire_digits_all(B) == True{} : Bool}, +okB: {LV.lv.ok(B) == True{} : Bool}, okU: {LV.lv.ok(U) == True{} : Bool}, lt: {Nat.is_le(1n+List.length(&2, Nat, B), List.length(&2, Nat, U)) == True{} : Bool}) -> {Nat.is_le(GoalText.gt_value(B), GoalText.gt_value(U)) == True{} : Bool}:
  match U:
    case Nil{}:
      LN.lv.absurd({Nat.is_le(GoalText.gt_value(B), 0n) == True{} : Bool}, lt)
    case +u <> +w:
      match w:
        case Nil{}:
          +lb = List.length(&2, Nat, B)
          LN.lv.absurd({Nat.is_le(GoalText.gt_value(B), GoalText.gt_value([u])) == True{} : Bool}, LN.lv.le_trans(1n, lb, 0n, lv.ok_len(B, okB), lt))
        case +z <> +t:
          +lb = List.length(&2, Nat, B)
          +nz = lv.not_true(Nat.is_eq(u, 0n), okU)
          +W = {z <> t : List<&2, Nat>}
          LN.lv.le_trans(GoalText.gt_value(B), LS.lv.p10(lb), GoalText.gt_value(u <> W), lv.le_of_succ(GoalText.gt_value(B), LS.lv.p10(lb), lv.V_bound(B, hB)),
            LN.lv.le_trans(LS.lv.p10(lb), LS.lv.p10(List.length(&2, Nat, W)), GoalText.gt_value(u <> W), lv.p10_mono(lb, List.length(&2, Nat, W), lt), lv.V_lower(u, W, nz)))

# The code's comparison
# ---------------------

def lv.below_true.at(+B: List<&2, Nat>, +U: List<&2, Nat>, a: Bool, ea: {Nat.is_lt(List.length(&2, Nat, B), List.length(&2, Nat, U)) == a : Bool}, hB: {LawsBase.wire_digits_all(B) == True{} : Bool}, hU: {LawsBase.wire_digits_all(U) == True{} : Bool}, okB: {LV.lv.ok(B) == True{} : Bool}, okU: {LV.lv.ok(U) == True{} : Bool}, +h: {Bool.or(a, Bool.and(Nat.is_eq(List.length(&2, Nat, B), List.length(&2, Nat, U)), Cmp.is_lt(lv.ord(B, U, EQ{})))) == True{} : Bool}) -> {Nat.is_le(GoalText.gt_value(B), GoalText.gt_value(U)) == True{} : Bool}:
  match a:
    case True{}:
      lv.len_lt(B, U, hB, okB, okU, lv.lt_succ_le(List.length(&2, Nat, B), List.length(&2, Nat, U), ea))
    case False{}:
      +e = Nat.is_eq(List.length(&2, Nat, B), List.length(&2, Nat, U))
      +c = Cmp.is_lt(lv.ord(B, U, EQ{}))
      lv.lex_lt(B, U, LS.lv.and_l(e, c, h), hB, hU, LS.lv.and_r(e, c, h))

# below: the first is worth at most the second
def lv.below_true(+B: List<&2, Nat>, +U: List<&2, Nat>, hB: {LawsBase.wire_digits_all(B) == True{} : Bool}, hU: {LawsBase.wire_digits_all(U) == True{} : Bool}, okB: {LV.lv.ok(B) == True{} : Bool}, okU: {LV.lv.ok(U) == True{} : Bool}, h: {lv.below(B, U) == True{} : Bool}) -> {Nat.is_le(GoalText.gt_value(B), GoalText.gt_value(U)) == True{} : Bool}:
  lv.below_true.at(B, U, Nat.is_lt(List.length(&2, Nat, B), List.length(&2, Nat, U)), {==}, hB, hU, okB, okU, h)

def lv.below_false.eq(+B: List<&2, Nat>, +U: List<&2, Nat>, e: Bool, ee: {Nat.is_eq(List.length(&2, Nat, B), List.length(&2, Nat, U)) == e : Bool}, hn: {Nat.is_lt(List.length(&2, Nat, B), List.length(&2, Nat, U)) == False{} : Bool}, hB: {LawsBase.wire_digits_all(B) == True{} : Bool}, hU: {LawsBase.wire_digits_all(U) == True{} : Bool}, okB: {LV.lv.ok(B) == True{} : Bool}, okU: {LV.lv.ok(U) == True{} : Bool}, h: {Bool.and(e, Cmp.is_lt(lv.ord(B, U, EQ{}))) == False{} : Bool}) -> {Nat.is_le(GoalText.gt_value(U), GoalText.gt_value(B)) == True{} : Bool}:
  match e:
    case True{}:
      lv.lex_ge(B, U, ee, hB, hU, h)
    case False{}:
      lv.len_lt(U, B, hU, okU, okB, lv.le_ne(List.length(&2, Nat, U), List.length(&2, Nat, B), lv.nlt_le(List.length(&2, Nat, B), List.length(&2, Nat, U), hn), ee))

def lv.below_false.at(+B: List<&2, Nat>, +U: List<&2, Nat>, a: Bool, ea: {Nat.is_lt(List.length(&2, Nat, B), List.length(&2, Nat, U)) == a : Bool}, hB: {LawsBase.wire_digits_all(B) == True{} : Bool}, hU: {LawsBase.wire_digits_all(U) == True{} : Bool}, okB: {LV.lv.ok(B) == True{} : Bool}, okU: {LV.lv.ok(U) == True{} : Bool}, h: {Bool.or(a, Bool.and(Nat.is_eq(List.length(&2, Nat, B), List.length(&2, Nat, U)), Cmp.is_lt(lv.ord(B, U, EQ{})))) == False{} : Bool}) -> ({Nat.is_le(GoalText.gt_value(U), GoalText.gt_value(B)) == True{} : Bool} & {Nat.is_le(List.length(&2, Nat, U), List.length(&2, Nat, B)) == True{} : Bool}):
  match a:
    case True{}:
      LN.lv.absurd(({Nat.is_le(GoalText.gt_value(U), GoalText.gt_value(B)) == True{} : Bool} & {Nat.is_le(List.length(&2, Nat, U), List.length(&2, Nat, B)) == True{} : Bool}), Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      +ea2 = ea
      (lv.below_false.eq(B, U, Nat.is_eq(List.length(&2, Nat, B), List.length(&2, Nat, U)), {==}, ea2, hB, hU, okB, okU, h), lv.nlt_le(List.length(&2, Nat, B), List.length(&2, Nat, U), ea2))

# not below: the second is worth at most the first, and has no more digits
def lv.below_false(+B: List<&2, Nat>, +U: List<&2, Nat>, hB: {LawsBase.wire_digits_all(B) == True{} : Bool}, hU: {LawsBase.wire_digits_all(U) == True{} : Bool}, okB: {LV.lv.ok(B) == True{} : Bool}, okU: {LV.lv.ok(U) == True{} : Bool}, h: {lv.below(B, U) == False{} : Bool}) -> ({Nat.is_le(GoalText.gt_value(U), GoalText.gt_value(B)) == True{} : Bool} & {Nat.is_le(List.length(&2, Nat, U), List.length(&2, Nat, B)) == True{} : Bool}):
  lv.below_false.at(B, U, Nat.is_lt(List.length(&2, Nat, B), List.length(&2, Nat, U)), {==}, hB, hU, okB, okU, h)

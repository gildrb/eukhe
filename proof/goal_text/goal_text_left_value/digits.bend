# eukhe: lemmas of LAW goal_text_left_value: the digit chars
#
# A digit d (below 10) is the char of code 48 + d (LawsBase.wire_dec_char).
# Each fact about one digit holds for each of the ten (lv.dcase computes
# them one by one): the code reads it back (Gt.digit), knows it for `0` or
# not, orders two of them as their values, and spec reads it back
# (gt_digits). The code's subtraction digit (Gt.sub.digit) of x less c is a
# digit char, and with its borrow it makes x + 10 * borrow == digit + c
# (lv.t_sub, x a digit, c at most 10: the digit below plus a borrow).

import Base
import ../../../bend/goal_text.bend as Gt
import ../../../laws/base.bend as LawsBase
import ../../../laws/goal_text.bend as GoalText
import ./nat.bend as LN

# a digit: one case per value
def lv.dcase(-P: Nat -> Type, d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}, p0: P(0n), p1: P(1n), p2: P(2n), p3: P(3n), p4: P(4n), p5: P(5n), p6: P(6n), p7: P(7n), p8: P(8n), p9: P(9n)) -> P(d):
  match d:
    case 0n:
      p0
    case 1n+d0:
      match d0:
        case 0n:
          p1
        case 1n+d1:
          match d1:
            case 0n:
              p2
            case 1n+d2:
              match d2:
                case 0n:
                  p3
                case 1n+d3:
                  match d3:
                    case 0n:
                      p4
                    case 1n+d4:
                      match d4:
                        case 0n:
                          p5
                        case 1n+d5:
                          match d5:
                            case 0n:
                              p6
                            case 1n+d6:
                              match d6:
                                case 0n:
                                  p7
                                case 1n+d7:
                                  match d7:
                                    case 0n:
                                      p8
                                    case 1n+d8:
                                      match d8:
                                        case 0n:
                                          p9
                                        case 1n+d9:
                                          match d9:
                                            case 0n:
                                              LN.lv.absurd(P(10n), h)
                                            case 1n+e:
                                              LN.lv.absurd(P(11n+e), h)

# a Nat at most 10: one case per value
def lv.ccase(-P: Nat -> Type, d: Nat, h: {Nat.is_lt(d, 11n) == True{} : Bool}, p0: P(0n), p1: P(1n), p2: P(2n), p3: P(3n), p4: P(4n), p5: P(5n), p6: P(6n), p7: P(7n), p8: P(8n), p9: P(9n), p10: P(10n)) -> P(d):
  match d:
    case 0n:
      p0
    case 1n+d0:
      match d0:
        case 0n:
          p1
        case 1n+d1:
          match d1:
            case 0n:
              p2
            case 1n+d2:
              match d2:
                case 0n:
                  p3
                case 1n+d3:
                  match d3:
                    case 0n:
                      p4
                    case 1n+d4:
                      match d4:
                        case 0n:
                          p5
                        case 1n+d5:
                          match d5:
                            case 0n:
                              p6
                            case 1n+d6:
                              match d6:
                                case 0n:
                                  p7
                                case 1n+d7:
                                  match d7:
                                    case 0n:
                                      p8
                                    case 1n+d8:
                                      match d8:
                                        case 0n:
                                          p9
                                        case 1n+d9:
                                          match d9:
                                            case 0n:
                                              p10
                                            case 1n+d10:
                                              match d10:
                                                case 0n:
                                                  LN.lv.absurd(P(11n), h)
                                                case 1n+e:
                                                  LN.lv.absurd(P(12n+e), h)

def lv.t_digit(d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {Gt.digit(LawsBase.wire_dec_char(d)) == d : Nat}:
  lv.dcase(x => {Gt.digit(LawsBase.wire_dec_char(x)) == x : Nat}, d, h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def lv.t_zero(d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {Char.is_eq(LawsBase.wire_dec_char(d), '0') == Nat.is_eq(d, 0n) : Bool}:
  lv.dcase(x => {Char.is_eq(LawsBase.wire_dec_char(x), '0') == Nat.is_eq(x, 0n) : Bool}, d, h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def lv.t_read(d: Nat, -t: String, h: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {GoalText.gt_digits(SCon{LawsBase.wire_dec_char(d), t}) == GoalText.gt_digits.put(d, GoalText.gt_digits(t)) : Maybe<&2, List<&2, Nat>>}:
  lv.dcase(x => {GoalText.gt_digits(SCon{LawsBase.wire_dec_char(x), t}) == GoalText.gt_digits.put(x, GoalText.gt_digits(t)) : Maybe<&2, List<&2, Nat>>}, d, h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def lv.t_cmp(x: Nat, +y: Nat, hx: {Nat.is_lt(x, 10n) == True{} : Bool}, +hy: {Nat.is_lt(y, 10n) == True{} : Bool}) -> {U32.cmp(U32.from_nat(Nat.add(48n, x)), U32.from_nat(Nat.add(48n, y))) == Nat.cmp(x, y) : Cmp}:
  lv.dcase(z => {U32.cmp(U32.from_nat(Nat.add(48n, z)), U32.from_nat(Nat.add(48n, y))) == Nat.cmp(z, y) : Cmp}, x, hx, lv.dcase(z => {U32.cmp(U32.from_nat(Nat.add(48n, 0n)), U32.from_nat(Nat.add(48n, z))) == Nat.cmp(0n, z) : Cmp}, y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}), lv.dcase(z => {U32.cmp(U32.from_nat(Nat.add(48n, 1n)), U32.from_nat(Nat.add(48n, z))) == Nat.cmp(1n, z) : Cmp}, y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}), lv.dcase(z => {U32.cmp(U32.from_nat(Nat.add(48n, 2n)), U32.from_nat(Nat.add(48n, z))) == Nat.cmp(2n, z) : Cmp}, y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}), lv.dcase(z => {U32.cmp(U32.from_nat(Nat.add(48n, 3n)), U32.from_nat(Nat.add(48n, z))) == Nat.cmp(3n, z) : Cmp}, y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}), lv.dcase(z => {U32.cmp(U32.from_nat(Nat.add(48n, 4n)), U32.from_nat(Nat.add(48n, z))) == Nat.cmp(4n, z) : Cmp}, y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}), lv.dcase(z => {U32.cmp(U32.from_nat(Nat.add(48n, 5n)), U32.from_nat(Nat.add(48n, z))) == Nat.cmp(5n, z) : Cmp}, y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}), lv.dcase(z => {U32.cmp(U32.from_nat(Nat.add(48n, 6n)), U32.from_nat(Nat.add(48n, z))) == Nat.cmp(6n, z) : Cmp}, y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}), lv.dcase(z => {U32.cmp(U32.from_nat(Nat.add(48n, 7n)), U32.from_nat(Nat.add(48n, z))) == Nat.cmp(7n, z) : Cmp}, y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}), lv.dcase(z => {U32.cmp(U32.from_nat(Nat.add(48n, 8n)), U32.from_nat(Nat.add(48n, z))) == Nat.cmp(8n, z) : Cmp}, y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}), lv.dcase(z => {U32.cmp(U32.from_nat(Nat.add(48n, 9n)), U32.from_nat(Nat.add(48n, z))) == Nat.cmp(9n, z) : Cmp}, y, hy, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))

# the code's subtraction digit of x less c, and its borrow
def lv.t_sub(x: Nat, +c: Nat, hx: {Nat.is_lt(x, 10n) == True{} : Bool}, +hc: {Nat.is_lt(c, 11n) == True{} : Bool}) -> ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, x), c), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, x), c), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, x), c), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, x), c), 10n), c) == Nat.add(x, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(x, c)))) : Nat})):
  lv.dcase(v => ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, v), c), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, v), c), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, v), c), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, v), c), 10n), c) == Nat.add(v, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(v, c)))) : Nat})), x, hx, lv.ccase(w => ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, 0n), w), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, 0n), w), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, 0n), w), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, 0n), w), 10n), w) == Nat.add(0n, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(0n, w)))) : Nat})), c, hc, ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==}))), lv.ccase(w => ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, 1n), w), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, 1n), w), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, 1n), w), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, 1n), w), 10n), w) == Nat.add(1n, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(1n, w)))) : Nat})), c, hc, ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==}))), lv.ccase(w => ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, 2n), w), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, 2n), w), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, 2n), w), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, 2n), w), 10n), w) == Nat.add(2n, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(2n, w)))) : Nat})), c, hc, ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==}))), lv.ccase(w => ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, 3n), w), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, 3n), w), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, 3n), w), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, 3n), w), 10n), w) == Nat.add(3n, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(3n, w)))) : Nat})), c, hc, ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==}))), lv.ccase(w => ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, 4n), w), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, 4n), w), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, 4n), w), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, 4n), w), 10n), w) == Nat.add(4n, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(4n, w)))) : Nat})), c, hc, ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==}))), lv.ccase(w => ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, 5n), w), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, 5n), w), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, 5n), w), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, 5n), w), 10n), w) == Nat.add(5n, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(5n, w)))) : Nat})), c, hc, ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==}))), lv.ccase(w => ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, 6n), w), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, 6n), w), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, 6n), w), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, 6n), w), 10n), w) == Nat.add(6n, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(6n, w)))) : Nat})), c, hc, ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==}))), lv.ccase(w => ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, 7n), w), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, 7n), w), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, 7n), w), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, 7n), w), 10n), w) == Nat.add(7n, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(7n, w)))) : Nat})), c, hc, ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==}))), lv.ccase(w => ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, 8n), w), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, 8n), w), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, 8n), w), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, 8n), w), 10n), w) == Nat.add(8n, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(8n, w)))) : Nat})), c, hc, ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==}))), lv.ccase(w => ({Gt.dchar(Nat.mod(Nat.sub(Nat.add(10n, 9n), w), 10n)) == LawsBase.wire_dec_char(Nat.mod(Nat.sub(Nat.add(10n, 9n), w), 10n)) : Char} & ({Nat.is_lt(Nat.mod(Nat.sub(Nat.add(10n, 9n), w), 10n), 10n) == True{} : Bool} & {Nat.add(Nat.mod(Nat.sub(Nat.add(10n, 9n), w), 10n), w) == Nat.add(9n, Nat.mul(10n, Gt.sub.borrow.of(Nat.is_lt(9n, w)))) : Nat})), c, hc, ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==})), ({==}, ({==}, {==}))))

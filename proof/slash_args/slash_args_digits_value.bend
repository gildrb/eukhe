# eukhe: the proof of LAW slash_args_digits_value
#
# PROOF: a digit other than `0` then digits is the code's positive test
# (LA.sab.positive_lead) and not the text `0` (sdf.ne0: the first chars
# differ), so both tests read the bound's numeral: fewer digits, or as many
# and at most it in text order; that is the order of the values
# (LAN.san.fit: a shorter numeral is the smaller, LAN.san.short; of one
# length, value order is text order, LAN.san.same).

import Base
import ../../bend/slash_args.bend as Sa
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA
import ./base/num.bend as LAN

def sdf.and_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LStg.stg.absurdF({b == True{} : Bool}, e)

# a text whose first char differs from `0` compares unequal to "0"
def sdf.ne.go(c: Cmp, t: String, h: {Cmp.is_eq(c) == False{} : Bool}) -> {Cmp.is_eq(String.order.go(t, SNil{}, c)) == False{} : Bool}:
  match c:
    case EQ{}:
      LStg.stg.absurd({Cmp.is_eq(String.order.go(t, SNil{}, EQ{})) == False{} : Bool}, h)
    case LT{}:
      match t:
        case SNil{}:
          {==}
        case SCon{x, u}:
          match x:
            case Chr{y}:
              {==}
    case GT{}:
      match t:
        case SNil{}:
          {==}
        case SCon{x, u}:
          match x:
            case Chr{y}:
              {==}

def sdf.ne0(d: Char, t: String, z: {Char.is_eq(d, '0') == False{} : Bool}) -> {String.eq(SCon{d, t}, "0") == False{} : Bool}:
  match d:
    case Chr{+x}:
      sdf.ne.go(U32.cmp(x, 48), t, z)

def sdf.digits(+d: Char, +t: String, dz: {Bool.and(Char.is_digit(d), Bool.not(Char.is_eq(d, '0'))) == True{} : Bool}, td: {SlashArgs.sa_digits(t) == True{} : Bool}) -> {SlashArgs.sa_digits(SCon{d, t}) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(Char.is_digit(d), SlashArgs.sa_digits(t)), SlashArgs.sa_digits(t), True{}, Equal.cong(Bool, Bool, y => Bool.and(y, SlashArgs.sa_digits(t)), Char.is_digit(d), True{}, LAN.san.and_l(Char.is_digit(d), Bool.not(Char.is_eq(d, '0')), dz)), td)

def SlashArgs.slash_args_digits_value(d, t, dz, td0):
  +td = td0
  +z = LA.sab.not_t(Char.is_eq(d, '0'), sdf.and_r(Char.is_digit(d), Bool.not(Char.is_eq(d, '0')), dz))
  +lead = Equal.trans(Bool, SlashArgs.sa_lead(SCon{d, t}), SlashArgs.sa_digits(t), True{}, Equal.cong(Bool, Bool, y => Bool.and(y, SlashArgs.sa_digits(t)), Bool.and(Char.is_digit(d), Bool.not(Char.is_eq(d, '0'))), True{}, dz), td)
  +pos = Equal.trans(Bool, Sa.positive(SCon{d, t}), SlashArgs.sa_lead(SCon{d, t}), True{}, LA.sab.positive_lead(SCon{d, t}), lead)
  +hs = sdf.digits(d, t, dz, td)
  (Equal.trans(Bool, Sa.u64(SCon{d, t}), Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{'1', "8446744073709551615"})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{'1', "8446744073709551615"})), String.is_le(SCon{d, t}, SCon{'1', "8446744073709551615"}))), Nat.is_le(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{'1', "8446744073709551615"})), Equal.cong(Bool, Bool, y => Bool.and(y, Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{'1', "8446744073709551615"})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{'1', "8446744073709551615"})), String.is_le(SCon{d, t}, SCon{'1', "8446744073709551615"})))), Sa.positive(SCon{d, t}), True{}, pos), LAN.san.fit(d, t, '1', "8446744073709551615", hs, dz, {==}, {==})), Equal.trans(Bool, Sa.keep_ok(SCon{d, t}), Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{'2', "147483647"})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{'2', "147483647"})), String.is_le(SCon{d, t}, SCon{'2', "147483647"}))), Nat.is_le(SlashArgs.sa_number(SCon{d, t}), SlashArgs.sa_number(SCon{'2', "147483647"})), Equal.trans(Bool, Sa.keep_ok(SCon{d, t}), Bool.and(Sa.positive(SCon{d, t}), Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{'2', "147483647"})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{'2', "147483647"})), String.is_le(SCon{d, t}, SCon{'2', "147483647"})))), Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{'2', "147483647"})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{'2', "147483647"})), String.is_le(SCon{d, t}, SCon{'2', "147483647"}))), Equal.cong(Bool, Bool, y => Bool.or(y, Bool.and(Sa.positive(SCon{d, t}), Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{'2', "147483647"})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{'2', "147483647"})), String.is_le(SCon{d, t}, SCon{'2', "147483647"}))))), String.eq(SCon{d, t}, "0"), False{}, sdf.ne0(d, t, z)), Equal.cong(Bool, Bool, y => Bool.and(y, Bool.or(Nat.is_lt(String.length(SCon{d, t}), String.length(SCon{'2', "147483647"})), Bool.and(Nat.is_eq(String.length(SCon{d, t}), String.length(SCon{'2', "147483647"})), String.is_le(SCon{d, t}, SCon{'2', "147483647"})))), Sa.positive(SCon{d, t}), True{}, pos)), LAN.san.fit(d, t, '2', "147483647", hs, dz, {==}, {==})))

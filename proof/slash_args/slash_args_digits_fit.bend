# eukhe: the proof of LAW slash_args_digits_fit
#
# PROOF: a digit other than `0` then digits is the code's positive test
# (LA.sab.positive_lead) and not the text `0` (sdf.ne0: the first chars
# differ); both tests then read the bound.

import Base
import ../../bend/slash_args.bend as Sa
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

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

def sdf.s(d: Char, t: String) -> String:
  SCon{d, t}

def SlashArgs.slash_args_digits_fit(d, t, dz, td):
  +s = sdf.s(d, t)
  +z = LA.sab.not_t(Char.is_eq(d, '0'), sdf.and_r(Char.is_digit(d), Bool.not(Char.is_eq(d, '0')), dz))
  +lead = Equal.trans(Bool, SlashArgs.sa_lead(s), SlashArgs.sa_digits(t), True{}, Equal.cong(Bool, Bool, y => Bool.and(y, SlashArgs.sa_digits(t)), Bool.and(Char.is_digit(d), Bool.not(Char.is_eq(d, '0'))), True{}, dz), td)
  +pos = Equal.trans(Bool, Sa.positive(s), SlashArgs.sa_lead(s), True{}, LA.sab.positive_lead(s), lead)
  (Equal.cong(Bool, Bool, y => Bool.and(y, Bool.or(Nat.is_lt(String.length(s), 20n), Bool.and(Nat.is_eq(String.length(s), 20n), String.is_le(s, "18446744073709551615")))), Sa.positive(s), True{}, pos), Equal.trans(Bool, Sa.keep_ok(s), Bool.and(Sa.positive(s), Bool.or(Nat.is_lt(String.length(s), 10n), Bool.and(Nat.is_eq(String.length(s), 10n), String.is_le(s, "2147483647")))), Bool.or(Nat.is_lt(String.length(s), 10n), Bool.and(Nat.is_eq(String.length(s), 10n), String.is_le(s, "2147483647"))), Equal.cong(Bool, Bool, y => Bool.or(y, Bool.and(Sa.positive(s), Bool.or(Nat.is_lt(String.length(s), 10n), Bool.and(Nat.is_eq(String.length(s), 10n), String.is_le(s, "2147483647"))))), String.eq(s, "0"), False{}, sdf.ne0(d, t, z)), Equal.cong(Bool, Bool, y => Bool.and(y, Bool.or(Nat.is_lt(String.length(s), 10n), Bool.and(Nat.is_eq(String.length(s), 10n), String.is_le(s, "2147483647")))), Sa.positive(s), True{}, pos)))

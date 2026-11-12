# eukhe: the proof of LAW semver_show_value

import Base
import ../../bend/replace.bend as Rp
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ../base/nat.bend as LNat
import ../base/logic/logic.bend as LLogicLogic
import ../base/replace.bend as LReplace
import ../base/semver.bend as LSemver
import ./base.bend as LASemver

# PROOF of LAW semver_show_value: Ver.show writes each number as
# Num.str(Num.dec(n), "") before the rest (psv.str_app). That text is a
# numeral of n: Num.str writes digit chars only (psv.digits); its first
# char is the most significant digit of Num.dec(n), never 0 past one digit
# (Rp.canon of Num.dec, proof/base/replace.bend rk.canon_dec; psv.lead);
# Horner's rule over it gives the value of the digits (psv.val_str,
# psv.h_val), which is n (ps.val_dec).

# digits written before x ++ acc: the digits before x, then acc
def psv.str_app(ds: List<&2, Sv.Dig>, x: String, acc: String) -> {Sv.Num.str(ds, String.append(x, acc)) == String.append(Sv.Num.str(ds, x), acc) : String}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      psv.str_app(rest, SCon{Sv.Dig.chr(d), x}, acc)

# Values
# ------

# the char of a digit has the digit's value
def psv.dval(d: Sv.Dig) -> {Semver.num_digit(Sv.Dig.chr(d)) == Sv.Dig.val(d) : Nat}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

# Horner's rule over the digits ds (last digit first) after a value acc
def psv.h(acc: Nat, ds: List<&2, Sv.Dig>) -> Nat:
  match ds:
    case Nil{}:
      acc
    case d <> rest:
      Nat.add(Sv.Dig.val(d), Nat.mul(psv.h(acc, rest), 10n))

# reading the digits Num.str writes before s goes through their value
def psv.val_str(+acc: Nat, ds: List<&2, Sv.Dig>, +s: String) -> {Semver.num_val(Sv.Num.str(ds, s), acc) == Semver.num_val(s, psv.h(acc, ds)) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +rest:
      %Equal.sym(Nat, Semver.num_val(Sv.Num.str(rest, SCon{Sv.Dig.chr(d), s}), acc), Semver.num_val(SCon{Sv.Dig.chr(d), s}, psv.h(acc, rest)), psv.val_str(acc, rest, SCon{Sv.Dig.chr(d), s})) : {_ == Semver.num_val(s, Nat.add(Sv.Dig.val(d), Nat.mul(psv.h(acc, rest), 10n))) : Nat}
      %Equal.sym(Nat, Semver.num_digit(Sv.Dig.chr(d)), Sv.Dig.val(d), psv.dval(d)) : {Semver.num_val(s, Nat.add(_, Nat.mul(psv.h(acc, rest), 10n))) == Semver.num_val(s, Nat.add(Sv.Dig.val(d), Nat.mul(psv.h(acc, rest), 10n))) : Nat}
      {==}

# Horner's rule from 0 gives Num.val
def psv.h_val(ds: List<&2, Sv.Dig>) -> {psv.h(0n, ds) == Sv.Num.val(ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> +rest:
      %Equal.sym(Nat, psv.h(0n, rest), Sv.Num.val(rest), psv.h_val(rest)) : {Nat.add(Sv.Dig.val(d), Nat.mul(_, 10n)) == Nat.add(Sv.Dig.val(d), Sv.Num.ten(Sv.Num.val(rest))) : Nat}
      %LSemver.rk.ten_mul(Sv.Num.val(rest)) : {Nat.add(Sv.Dig.val(d), _) == Nat.add(Sv.Dig.val(d), Sv.Num.ten(Sv.Num.val(rest))) : Nat}
      {==}

# the numeral Num.dec writes for n has the value n
def psv.value(+n: Nat) -> {Semver.num_val(Sv.Num.str(Sv.Num.dec(n), SNil{}), 0n) == n : Nat}:
  +e1 = psv.val_str(0n, Sv.Num.dec(n), SNil{})
  +e2 = Equal.trans(Nat, Semver.num_val(Sv.Num.str(Sv.Num.dec(n), SNil{}), 0n), psv.h(0n, Sv.Num.dec(n)), Sv.Num.val(Sv.Num.dec(n)), e1, psv.h_val(Sv.Num.dec(n)))
  Equal.trans(Nat, Semver.num_val(Sv.Num.str(Sv.Num.dec(n), SNil{}), 0n), Sv.Num.val(Sv.Num.dec(n)), n, e2, Equal.sym(Nat, n, Sv.Num.val(Sv.Num.dec(n)), LASemver.ps.val_dec(n)))

# Digits
# ------

def psv.dig(d: Sv.Dig, -s: String) -> {Bool.and(Char.is_digit(Sv.Dig.chr(d)), Semver.num_digits(s)) == Semver.num_digits(s) : Bool}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

# Num.str writes digit chars only
def psv.digits(ds: List<&2, Sv.Dig>, +s: String) -> {Semver.num_digits(Sv.Num.str(ds, s)) == Semver.num_digits(s) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +rest:
      Equal.trans(Bool, Semver.num_digits(Sv.Num.str(rest, SCon{Sv.Dig.chr(d), s})), Bool.and(Char.is_digit(Sv.Dig.chr(d)), Semver.num_digits(s)), Semver.num_digits(s), psv.digits(rest, SCon{Sv.Dig.chr(d), s}), psv.dig(d, s))

# No leading zero
# ---------------

# a digit's char, with more text after it, leads a numeral exactly when the
# digit is not 0
def psv.zero(d: Sv.Dig) -> {Bool.or(Bool.not(Char.is_eq(Sv.Dig.chr(d), '0')), False{}) == Bool.not(Rp.zero(d)) : Bool}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

# two or more chars: the text leads with the char of the most significant
# digit
def psv.lead_str(rr: List<&2, Sv.Dig>, r: Sv.Dig, x: Char, s: String) -> {Semver.num_lead(Sv.Num.str(r <> rr, SCon{x, s})) == Bool.not(Rp.zero(Rp.top(rr, r))) : Bool}:
  match rr:
    case Nil{}:
      psv.zero(r)
    case r2 <> rr2:
      psv.lead_str(rr2, r2, Sv.Dig.chr(r), SCon{x, s})

# one digit alone is a numeral's lead
def psv.lead_one(d: Sv.Dig) -> {Semver.num_lead(SCon{Sv.Dig.chr(d), SNil{}}) == True{} : Bool}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

# canonical digits are written with no leading zero
def psv.lead(ds: List<&2, Sv.Dig>, h: {Rp.canon(ds) == True{} : Bool}) -> {Semver.num_lead(Sv.Num.str(ds, SNil{})) == True{} : Bool}:
  match ds:
    case Nil{}:
      LLogicLogic.semver.ps.absurdF({Semver.num_lead(Sv.Num.str(Nil{}, SNil{})) == True{} : Bool}, h)
    case d <> rest:
      match rest:
        case Nil{}:
          psv.lead_one(d)
        case r <> rr:
          Equal.trans(Bool, Semver.num_lead(Sv.Num.str(r <> rr, SCon{Sv.Dig.chr(d), SNil{}})), Bool.not(Rp.zero(Rp.top(rr, r))), True{}, psv.lead_str(rr, r, Sv.Dig.chr(d), SNil{}), h)

# Numerals
# --------

# Num.str(Num.dec(n), "") is the numeral of n
def psv.numeral(+n: Nat) -> {Semver.numeral(Sv.Num.str(Sv.Num.dec(n), SNil{}), n) == True{} : Bool}:
  +s = Sv.Num.str(Sv.Num.dec(n), SNil{})
  %Equal.sym(Bool, Semver.num_digits(s), True{}, psv.digits(Sv.Num.dec(n), SNil{})) : {Bool.and(_, Bool.and(Semver.num_lead(s), Nat.is_eq(Semver.num_val(s, 0n), n))) == True{} : Bool}
  %Equal.sym(Bool, Semver.num_lead(s), True{}, psv.lead(Sv.Num.dec(n), LReplace.rk.canon_dec(n))) : {Bool.and(_, Nat.is_eq(Semver.num_val(s, 0n), n)) == True{} : Bool}
  %Equal.sym(Nat, Semver.num_val(s, 0n), n, psv.value(n)) : {Nat.is_eq(_, n) == True{} : Bool}
  LNat.ppr.nat_eq_refl(n)

def psv.numerals(+a: Nat, +b: Nat, +c: Nat) -> {Bool.and(Semver.numeral(Sv.Num.str(Sv.Num.dec(a), SNil{}), a), Bool.and(Semver.numeral(Sv.Num.str(Sv.Num.dec(b), SNil{}), b), Semver.numeral(Sv.Num.str(Sv.Num.dec(c), SNil{}), c))) == True{} : Bool}:
  %Equal.sym(Bool, Semver.numeral(Sv.Num.str(Sv.Num.dec(a), SNil{}), a), True{}, psv.numeral(a)) : {Bool.and(_, Bool.and(Semver.numeral(Sv.Num.str(Sv.Num.dec(b), SNil{}), b), Semver.numeral(Sv.Num.str(Sv.Num.dec(c), SNil{}), c))) == True{} : Bool}
  %Equal.sym(Bool, Semver.numeral(Sv.Num.str(Sv.Num.dec(b), SNil{}), b), True{}, psv.numeral(b)) : {Bool.and(_, Semver.numeral(Sv.Num.str(Sv.Num.dec(c), SNil{}), c)) == True{} : Bool}
  psv.numeral(c)

# a version is written as its three numbers' texts joined by dots
def psv.show(+a: Nat, +b: Nat, +c: Nat) -> {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(Sv.Num.str(Sv.Num.dec(a), SNil{}), SCon{'.', String.append(Sv.Num.str(Sv.Num.dec(b), SNil{}), SCon{'.', Sv.Num.str(Sv.Num.dec(c), SNil{})})}) : String}:
  %psv.str_app(Sv.Num.dec(b), SNil{}, SCon{'.', Sv.Num.str(Sv.Num.dec(c), SNil{})}) : {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(Sv.Num.str(Sv.Num.dec(a), SNil{}), SCon{'.', _}) : String}
  psv.str_app(Sv.Num.dec(a), SNil{}, SCon{'.', Sv.Num.str(Sv.Num.dec(b), SCon{'.', Sv.Num.str(Sv.Num.dec(c), SNil{})})})

def Semver.semver_show_value(a, b, c):
  (Sv.Num.str(Sv.Num.dec(a), SNil{}), (Sv.Num.str(Sv.Num.dec(b), SNil{}), (Sv.Num.str(Sv.Num.dec(c), SNil{}), (psv.show(a, b, c), psv.numerals(a, b, c)))))

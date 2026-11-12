# eukhe: the proof of LAW arg_repair_coerce_int
#
# PROOF: the text has no White_Space, so it is its own `str::trim`
# (AC.ac.trim_clean); its sign is read (by cases; a digit is no sign,
# AC.ac.dig_minus/plus), the rest is one or more ASCII digits
# (AC.ac.digits_ok) whose canonical form is the digits after the zeros
# (AC.ac.canon_lead), not "0" (AC.ac.nz_text); the code's bound test is
# the spec's digit-order comparison, its reading the spec's (AC.ac.fit).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../laws/arg_repair/coerce.bend as ArgRepairCoerce
import ./base.bend as AB
import ./base/coerce.bend as AC

# no sign: the text, zeros or a digit first, is read as digits
def ci.plain(z: Nat, +d: ArgRepairCoerce.Dig, +ds: List<&2, ArgRepairCoerce.Dig>) -> {Ar.int(String.append(ArgRepairCoerce.sp_zeros(z), ArgRepairCoerce.sp_digs(d <> ds))) == Ar.int.digits(False{}, String.append(ArgRepairCoerce.sp_zeros(z), ArgRepairCoerce.sp_digs(d <> ds))) : Maybe<&2, Ar.To>}:
  match z:
    case 0n:
      +x = ArgRepairCoerce.sp_digs(ds)
      %Equal.sym(Bool, Char.is_eq(ArgRepairCoerce.sp_dig(d), '-'), False{}, AC.ac.dig_minus(d)) : {Ar.int.signed(_, Char.is_eq(ArgRepairCoerce.sp_dig(d), '+'), ArgRepairCoerce.sp_dig(d), x) == Ar.int.digits(False{}, SCon{ArgRepairCoerce.sp_dig(d), x}) : Maybe<&2, Ar.To>}
      %Equal.sym(Bool, Char.is_eq(ArgRepairCoerce.sp_dig(d), '+'), False{}, AC.ac.dig_plus(d)) : {Ar.int.signed(False{}, _, ArgRepairCoerce.sp_dig(d), x) == Ar.int.digits(False{}, SCon{ArgRepairCoerce.sp_dig(d), x}) : Maybe<&2, Ar.To>}
      {==}
    case 1n+p:
      {==}

# the reading of the sign, then of the digits
def ci.sign(s: ArgRepairCoerce.Sign, +z: Nat, +d: ArgRepairCoerce.Dig, +ds: List<&2, ArgRepairCoerce.Dig>, nz: {ArgRepairCoerce.sp_zero(d) == False{} : Bool}, hd: {Ar.digits(String.append(ArgRepairCoerce.sp_zeros(z), ArgRepairCoerce.sp_digs(d <> ds))) == True{} : Bool}, hn: {String.is_empty(String.append(ArgRepairCoerce.sp_zeros(z), ArgRepairCoerce.sp_digs(d <> ds))) == False{} : Bool}, ec: {Ar.canon(String.append(ArgRepairCoerce.sp_zeros(z), ArgRepairCoerce.sp_digs(d <> ds))) == ArgRepairCoerce.sp_digs(d <> ds) : String}) -> {Ar.int(String.append(ArgRepairCoerce.sp_sign(s), String.append(ArgRepairCoerce.sp_zeros(z), ArgRepairCoerce.sp_digs(d <> ds)))) == ArgRepairCoerce.sp_int(s, ArgRepairCoerce.sp_digs(d <> ds)) : Maybe<&2, Ar.To>}:
  match s:
    case ArgRepairCoerce.SgMinus{}:
      +dd = ArgRepairCoerce.sp_digs(d <> ds)
      +y = String.append(ArgRepairCoerce.sp_zeros(z), dd)
      %Equal.sym(Maybe<&2, Ar.To>, Ar.int.digits(True{}, y), Ar.int.sign(True{}, Ar.canon(y)), AC.ac.digits_ok(True{}, y, hn, hd)) : {_ == ArgRepairCoerce.sp_int(ArgRepairCoerce.SgMinus{}, dd) : Maybe<&2, Ar.To>}
      %Equal.sym(String, Ar.canon(y), dd, ec) : {Ar.int.sign(True{}, _) == ArgRepairCoerce.sp_int(ArgRepairCoerce.SgMinus{}, dd) : Maybe<&2, Ar.To>}
      %Equal.sym(Bool, String.eq(dd, "0"), False{}, AC.ac.nz_text(d, ArgRepairCoerce.sp_digs(ds), nz)) : {Ar.int.neg.at(_, dd) == ArgRepairCoerce.sp_int(ArgRepairCoerce.SgMinus{}, dd) : Maybe<&2, Ar.To>}
      AC.ac.fit(Ar.at_most(dd, "9223372036854775808"), SCon{'-', dd})
    case ArgRepairCoerce.SgPlus{}:
      +dd = ArgRepairCoerce.sp_digs(d <> ds)
      +y = String.append(ArgRepairCoerce.sp_zeros(z), dd)
      %Equal.sym(Maybe<&2, Ar.To>, Ar.int.digits(False{}, y), Ar.int.sign(False{}, Ar.canon(y)), AC.ac.digits_ok(False{}, y, hn, hd)) : {_ == ArgRepairCoerce.sp_int(ArgRepairCoerce.SgPlus{}, dd) : Maybe<&2, Ar.To>}
      %Equal.sym(String, Ar.canon(y), dd, ec) : {Ar.int.sign(False{}, _) == ArgRepairCoerce.sp_int(ArgRepairCoerce.SgPlus{}, dd) : Maybe<&2, Ar.To>}
      AC.ac.fit(Ar.at_most(dd, "9223372036854775807"), dd)
    case ArgRepairCoerce.SgNone{}:
      +dd = ArgRepairCoerce.sp_digs(d <> ds)
      +y = String.append(ArgRepairCoerce.sp_zeros(z), dd)
      %Equal.sym(Maybe<&2, Ar.To>, Ar.int(y), Ar.int.digits(False{}, y), ci.plain(z, d, ds)) : {_ == ArgRepairCoerce.sp_int(ArgRepairCoerce.SgNone{}, dd) : Maybe<&2, Ar.To>}
      %Equal.sym(Maybe<&2, Ar.To>, Ar.int.digits(False{}, y), Ar.int.sign(False{}, Ar.canon(y)), AC.ac.digits_ok(False{}, y, hn, hd)) : {_ == ArgRepairCoerce.sp_int(ArgRepairCoerce.SgNone{}, dd) : Maybe<&2, Ar.To>}
      %Equal.sym(String, Ar.canon(y), dd, ec) : {Ar.int.sign(False{}, _) == ArgRepairCoerce.sp_int(ArgRepairCoerce.SgNone{}, dd) : Maybe<&2, Ar.To>}
      AC.ac.fit(Ar.at_most(dd, "9223372036854775807"), dd)

def ArgRepairCoerce.arg_repair_coerce_int(n, it, num, sh, s, z, d, ds, nz):
  +nz2 = nz
  +dd = ArgRepairCoerce.sp_digs(d <> ds)
  +y = String.append(ArgRepairCoerce.sp_zeros(z), dd)
  +x = String.append(ArgRepairCoerce.sp_sign(s), y)
  +cl = AC.ac.clean_app(ArgRepairCoerce.sp_sign(s), y, AC.ac.clean_sign(s), AC.ac.clean_app(ArgRepairCoerce.sp_zeros(z), dd, AC.ac.clean_zeros(z), AC.ac.clean_digs(d <> ds)))
  +hd = AC.ac.digits_app(ArgRepairCoerce.sp_zeros(z), dd, AC.ac.zeros_digits(z), AC.ac.digs_digits(d <> ds))
  +hn = AC.ac.nonempty(z, d, ds)
  +ec = AC.ac.canon_lead(z, d, ds, nz2)
  %Equal.sym(String, Ar.trim(x), x, AC.ac.trim_clean(x, cl)) : {Ar.int(_) == ArgRepairCoerce.sp_int(s, dd) : Maybe<&2, Ar.To>}
  ci.sign(s, z, d, ds, nz2, hd, hn, ec)

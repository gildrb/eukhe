# eukhe: the proof of LAW arg_repair_coerce_int_zero
#
# PROOF: the text has no White_Space (AC.ac.trim_clean); its sign is read
# by cases, the zeros are one or more ASCII digits (AC.ac.digits_ok) whose
# canonical form is "0" (AC.ac.canon_zero), which fits i64 either way.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../laws/arg_repair/coerce.bend as ArgRepairCoerce
import ./base.bend as AB
import ./base/coerce.bend as AC

def cz.sign(s: ArgRepairCoerce.Sign, +z: Nat) -> {Ar.int(String.append(ArgRepairCoerce.sp_sign(s), SCon{'0', ArgRepairCoerce.sp_zeros(z)})) == Some{Ar.TNum{"0"}} : Maybe<&2, Ar.To>}:
  match s:
    case ArgRepairCoerce.SgMinus{}:
      +y = String.append("0", ArgRepairCoerce.sp_zeros(z))
      %Equal.sym(Maybe<&2, Ar.To>, Ar.int.digits(True{}, y), Ar.int.sign(True{}, Ar.canon(y)), AC.ac.digits_ok(True{}, y, {==}, AC.ac.zeros_digits(1n+z))) : {_ == Some{Ar.TNum{"0"}} : Maybe<&2, Ar.To>}
      %Equal.sym(String, Ar.canon(y), "0", AC.ac.canon_zero(z)) : {Ar.int.sign(True{}, _) == Some{Ar.TNum{"0"}} : Maybe<&2, Ar.To>}
      {==}
    case ArgRepairCoerce.SgPlus{}:
      +y = String.append("0", ArgRepairCoerce.sp_zeros(z))
      %Equal.sym(Maybe<&2, Ar.To>, Ar.int.digits(False{}, y), Ar.int.sign(False{}, Ar.canon(y)), AC.ac.digits_ok(False{}, y, {==}, AC.ac.zeros_digits(1n+z))) : {_ == Some{Ar.TNum{"0"}} : Maybe<&2, Ar.To>}
      %Equal.sym(String, Ar.canon(y), "0", AC.ac.canon_zero(z)) : {Ar.int.sign(False{}, _) == Some{Ar.TNum{"0"}} : Maybe<&2, Ar.To>}
      {==}
    case ArgRepairCoerce.SgNone{}:
      +y = String.append("0", ArgRepairCoerce.sp_zeros(z))
      %Equal.sym(Maybe<&2, Ar.To>, Ar.int.digits(False{}, y), Ar.int.sign(False{}, Ar.canon(y)), AC.ac.digits_ok(False{}, y, {==}, AC.ac.zeros_digits(1n+z))) : {_ == Some{Ar.TNum{"0"}} : Maybe<&2, Ar.To>}
      %Equal.sym(String, Ar.canon(y), "0", AC.ac.canon_zero(z)) : {Ar.int.sign(False{}, _) == Some{Ar.TNum{"0"}} : Maybe<&2, Ar.To>}
      {==}

def ArgRepairCoerce.arg_repair_coerce_int_zero(n, it, num, sh, s, z):
  +y = String.append("0", ArgRepairCoerce.sp_zeros(z))
  +x = String.append(ArgRepairCoerce.sp_sign(s), y)
  +cl = AC.ac.clean_app(ArgRepairCoerce.sp_sign(s), y, AC.ac.clean_sign(s), AC.ac.clean_zeros(1n+z))
  %Equal.sym(String, Ar.trim(x), x, AC.ac.trim_clean(x, cl)) : {Ar.int(_) == Some{Ar.TNum{"0"}} : Maybe<&2, Ar.To>}
  cz.sign(s, z)

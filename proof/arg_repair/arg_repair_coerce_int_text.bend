# eukhe: the proof of LAW arg_repair_coerce_int_text
#
# PROOF: no text: no reading; a bare text is its own `str::trim`
# (AC.ac.trim_self); the code reads its sign as the spec's grammar does
# (by cases) and its digits as the spec's (AC.ac.digits_eq), so a text
# outside `[+-]?[0-9]+` reads as none.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../laws/arg_repair/coerce.bend as ArgRepairCoerce
import ./base.bend as AB
import ./base/coerce.bend as AC

def ct.digits(+neg: Bool, +s: String, h: {ArgRepairCoerce.sp_some_digits(s) == False{} : Bool}) -> {Ar.int.digits(neg, s) == None{} : Maybe<&2, Ar.To>}:
  %AC.ac.digits_eq(s) : {Ar.int.digits.at(Bool.and(Bool.not(String.is_empty(s)), _), neg, s) == None{} : Maybe<&2, Ar.To>}
  %Equal.sym(Bool, ArgRepairCoerce.sp_some_digits(s), False{}, h) : {Ar.int.digits.at(_, neg, s) == None{} : Maybe<&2, Ar.To>}
  {==}

def ct.signed(mi: Bool, pl: Bool, +c: Char, +t: String, h: {ArgRepairCoerce.sp_int_text.at(mi, pl, c, t) == False{} : Bool}) -> {Ar.int.signed(mi, pl, c, t) == None{} : Maybe<&2, Ar.To>}:
  match mi:
    case True{}:
      ct.digits(True{}, t, h)
    case False{}:
      match pl:
        case True{}:
          ct.digits(False{}, t, h)
        case False{}:
          ct.digits(False{}, SCon{c, t}, h)

def ct.int(u: String, h: {ArgRepairCoerce.sp_int_text(u) == False{} : Bool}) -> {Ar.int(u) == None{} : Maybe<&2, Ar.To>}:
  match u:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      ct.signed(Char.is_eq(c, '-'), Char.is_eq(c, '+'), c, t, h)

def ArgRepairCoerce.arg_repair_coerce_int_text(n, it, m, num, sh, hm, hi):
  match m:
    case None{}:
      {==}
    case Some{+u}:
      %Equal.sym(String, Ar.trim(u), u, AC.ac.trim_self(u, hm)) : {Ar.int(_) == None{} : Maybe<&2, Ar.To>}
      ct.int(u, hi)

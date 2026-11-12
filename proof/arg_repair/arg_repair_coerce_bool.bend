# eukhe: the proof of LAW arg_repair_coerce_bool
#
# PROOF: no text: no reading; a bare text is its own `str::trim`
# (AC.ac.trim_self), the code's ASCII lower case is Rust's (AC.ac.lower)
# and its words are the requirement's, in another order (AC.ac.word).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../laws/arg_repair/coerce.bend as ArgRepairCoerce
import ./base.bend as AB
import ./base/coerce.bend as AC

def ArgRepairCoerce.arg_repair_coerce_bool(n, it, m, num, sh, hm):
  match m:
    case None{}:
      {==}
    case Some{+u}:
      %Equal.sym(String, Ar.trim(u), u, AC.ac.trim_self(u, hm)) : {Ar.word(Ar.lower(_)) == ArgRepairCoerce.sp_bool(Some{u}) : Maybe<&2, Ar.To>}
      %AC.ac.lower(u) : {Ar.word(Ar.lower(u)) == ArgRepairCoerce.sp_bool.word(_) : Maybe<&2, Ar.To>}
      AC.ac.word(Ar.lower(u))

# eukhe: the proof of LAW arg_repair_coerce_trims
#
# PROOF: a typed argument's string is read through `str::trim` of its text
# alone (the boolean and the integer readings; the others read no text);
# `str::trim` of White_Space, a bare text, White_Space is the bare text,
# as is `str::trim` of the bare text (AC.ac.trim, AC.ac.trim_self).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../laws/arg_repair/coerce.bend as ArgRepairCoerce
import ./base.bend as AB
import ./base/coerce.bend as AC

def ArgRepairCoerce.arg_repair_coerce_trims(p, a, u, b, n, sh, ha, hb, hu):
  match p:
    case None{}:
      {==}
    case Some{q}:
      match q:
        case Ar.Prop{nm, k, it}:
          match k:
            case None{}:
              {==}
            case Some{+t}:
              +hu2 = hu
              +x = String.append(a, String.append(u, b))
              AC.ac.spell_eq(Ar.kind(t), it, x, u, n, sh, Equal.trans(String, Ar.trim(x), u, Ar.trim(u), AC.ac.trim(a, u, b, ha, hb, hu2), Equal.sym(String, Ar.trim(u), u, AC.ac.trim_self(u, hu2))))

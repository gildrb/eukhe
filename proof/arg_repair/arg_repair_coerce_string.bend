# eukhe: the proof of LAW arg_repair_coerce_string
#
# PROOF: by cases on the value (and on the boolean).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../laws/arg_repair/coerce.bend as ArgRepairCoerce
import ./base.bend as AB
import ./base/coerce.bend as AC

def ArgRepairCoerce.arg_repair_coerce_string(n, it, v):
  match v:
    case Ar.VNull{}:
      {==}
    case Ar.VBool{b}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case Ar.VNum{x}:
      {==}
    case Ar.VStr{t, m, sh}:
      {==}
    case Ar.VArr{}:
      {==}
    case Ar.VObj{}:
      {==}

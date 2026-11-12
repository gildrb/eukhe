# eukhe: the proof of LAW arg_repair_coerce_object
#
# PROOF: by cases on the value (and on a string's shape).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../laws/arg_repair/coerce.bend as ArgRepairCoerce
import ./base.bend as AB
import ./base/coerce.bend as AC

def ArgRepairCoerce.arg_repair_coerce_object(n, it, v):
  match v:
    case Ar.VNull{}:
      {==}
    case Ar.VBool{b}:
      {==}
    case Ar.VNum{x}:
      {==}
    case Ar.VStr{t, m, sh}:
      match sh:
        case Ar.SPlain{}:
          {==}
        case Ar.SBrace{o}:
          match o:
            case True{}:
              {==}
            case False{}:
              {==}
        case Ar.SBracket{a}:
          {==}
    case Ar.VArr{}:
      {==}
    case Ar.VObj{}:
      {==}

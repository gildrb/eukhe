# eukhe: the proof of LAW quirks_fine_all_exact

import Base
import ../../bend/infer.bend as If
import ../../laws/quirks.bend as Quirks

def Quirks.quirks_fine_all_exact(vs):
  match vs:
    case Nil{}:
      {==}
    case v <> rest:
      match v:
        case If.Fine{}:
          %Quirks.quirks_fine_all_exact(rest) : {If.fine_all(If.Fine{} <> rest) == _ : Bool}
          {==}
        case If.Unheard{}:
          {==}
        case If.ClashAt{j}:
          {==}

# eukhe: lemmas the proofs of area cron share: list

import Base
import ../../../bend/cron.bend as Cr
import ./logic.bend as LALogic

def pc.all_append(+c: Nat, +dead: List<&2, Nat>, xs: List<&2, Cr.Rec>, +ys: List<&2, Cr.Rec>, gx: LALogic.pc.AllG(c, dead, xs), gy: LALogic.pc.AllG(c, dead, ys)) -> LALogic.pc.AllG(c, dead, List.append(&2, Cr.Rec, xs, ys)):
  match xs:
    case Nil{}:
      gy
    case r <> t:
      match r:
        case Cr.Known{+j}:
          (a, b) = gx
          (a, pc.all_append(c, dead, t, ys, b, gy))
        case Cr.Raw{x}:
          pc.all_append(c, dead, t, ys, gx, gy)

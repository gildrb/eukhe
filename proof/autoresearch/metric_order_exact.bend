# eukhe: the proof of LAW metric_order_exact

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/dec.bend as AdDec

def Autoresearch.metric_order_exact(a, b, wa, wb):
  match a:
    case ArD.Dec{na, +da, +sa}:
      match na:
        case True{}:
          match b:
            case ArD.Dec{nb, +db, +sb}:
              match nb:
                case True{}:
                  AdDec.ad.mag_exact(db, sb, da, sa, wb, wa)
                case False{}:
                  AdDec.ad.cross_exact(da, db, LT{})
        case False{}:
          match b:
            case ArD.Dec{nb, +db, +sb}:
              match nb:
                case True{}:
                  AdDec.ad.cross_exact(da, db, GT{})
                case False{}:
                  AdDec.ad.mag_exact(da, sa, db, sb, wa, wb)

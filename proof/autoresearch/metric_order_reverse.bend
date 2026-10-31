# eukhe: the proof of LAW metric_order_reverse

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/dec.bend as AdDec

def Autoresearch.metric_order_reverse(a, b):
  match a:
    case ArD.Dec{na, da, +sa}:
      match na:
        case True{}:
          match b:
            case ArD.Dec{nb, db, +sb}:
              match nb:
                case True{}:
                  AdDec.ad.pad_flip(ArD.cat(db, ArD.zeros(sa)), ArD.cat(da, ArD.zeros(sb)))
                case False{}:
                  AdDec.ad.cross_flip(ArD.nz(da), ArD.nz(db))
        case False{}:
          match b:
            case ArD.Dec{nb, db, +sb}:
              match nb:
                case True{}:
                  AdDec.ad.cross_flip_gt(ArD.nz(da), ArD.nz(db))
                case False{}:
                  AdDec.ad.pad_flip(ArD.cat(da, ArD.zeros(sb)), ArD.cat(db, ArD.zeros(sa)))

# eukhe: the proof of LAW metric_order_self

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/dec.bend as AdDec

def Autoresearch.metric_order_self(a):
  match a:
    case ArD.Dec{neg, ds, +scale}:
      match neg:
        case True{}:
          AdDec.ad.pad_refl(ArD.cat(ds, ArD.zeros(scale)))
        case False{}:
          AdDec.ad.pad_refl(ArD.cat(ds, ArD.zeros(scale)))

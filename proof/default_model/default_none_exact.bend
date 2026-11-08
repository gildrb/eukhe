# eukhe: the proof of LAW default_none_exact

import Base
import ../../bend/default_model.bend as Dm
import ../../laws/default_model.bend as DefaultModel

def DefaultModel.default_none_exact(ks):
  match ks:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

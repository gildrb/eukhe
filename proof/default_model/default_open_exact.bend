# eukhe: the proof of LAW default_open_exact

import Base
import ../../bend/default_model.bend as Dm
import ../../laws/default_model.bend as DefaultModel

def DefaultModel.default_open_exact(r):
  match r:
    case Dm.Runs{p, s}:
      match s:
        case Dm.Kept{}:
          {==}
        case Dm.Swapped{k}:
          {==}
    case Dm.Nothing{}:
      {==}
    case Dm.Refused{k}:
      {==}

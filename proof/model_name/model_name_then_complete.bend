# eukhe: the proof of LAW model_name_then_complete

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/rules.bend as LR

def ModelName.model_name_then_complete(a, b, x, y, z, h):
  LR.mnr.then_app(x, a, b, y, z, h)

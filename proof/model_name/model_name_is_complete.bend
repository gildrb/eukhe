# eukhe: the proof of LAW model_name_is_complete

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/rules.bend as LR

def ModelName.model_name_is_complete(pre, s, post):
  LR.mnr.iss_in(pre, s, post)

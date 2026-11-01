# eukhe: the proof of LAW model_name_is_sound

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/rules.bend as LR

def ModelName.model_name_is_sound(ps, s, h):
  %h : LR.mnr.IssP(ps, s, _)
  LR.mnr.iss_sp(ps, s)

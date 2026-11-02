# eukhe: the proof of LAW model_name_then_sound

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/rules.bend as LR

def ModelName.model_name_then_sound(a, b, s, h):
  %h : LR.mnr.ThenP(a, b, s, _)
  LR.mnr.then_sp(a, b, s)

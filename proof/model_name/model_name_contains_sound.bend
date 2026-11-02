# eukhe: the proof of LAW model_name_contains_sound

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base.bend as LA

def ModelName.model_name_contains_sound(ps, s, h):
  %h : LA.mnb.PartsP(ps, s, _)
  LA.mnb.parts_sp(ps, s)

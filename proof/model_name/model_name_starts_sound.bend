# eukhe: the proof of LAW model_name_starts_sound

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/rules.bend as LR

def ModelName.model_name_starts_sound(ps, s, h):
  %h : LR.mnr.HeadsP(ps, s, _)
  LR.mnr.heads_sp(ps, s)

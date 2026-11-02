# eukhe: the proof of LAW model_name_number_sound

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/number.bend as LN

def ModelName.model_name_number_sound(ps, s, n, w, h):
  %h : LN.mnn.NumsP(ps, s, n, w, _)
  LN.mnn.nums_sp(ps, s, n, w)

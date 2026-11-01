# eukhe: the proof of LAW model_name_dash_decides

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/decide.bend as LD

def ModelName.model_name_dash_decides(s):
  LD.mnd.dash_go(s, None{})

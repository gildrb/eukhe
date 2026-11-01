# eukhe: the proof of LAW model_name_rule_decides

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/decide.bend as LD

def ModelName.model_name_rule_decides(r, s):
  LD.mnd.rule(r, s)

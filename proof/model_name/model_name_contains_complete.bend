# eukhe: the proof of LAW model_name_contains_complete

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base.bend as LA

def ModelName.model_name_contains_complete(pre, p, post, a, b):
  LA.mnb.parts_in(pre, p, post, String.append(a, String.append(p, b)), LA.mnb.part_app(a, p, b))

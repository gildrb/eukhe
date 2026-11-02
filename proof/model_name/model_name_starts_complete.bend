# eukhe: the proof of LAW model_name_starts_complete

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base.bend as LA
import ./base/rules.bend as LR

def ModelName.model_name_starts_complete(pre, p, post, b):
  LR.mnr.heads_in(pre, p, post, String.append(p, b), LA.mnb.got_app(p, b))

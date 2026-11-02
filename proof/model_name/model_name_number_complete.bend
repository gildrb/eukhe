# eukhe: the proof of LAW model_name_number_complete

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/number.bend as LN

def ModelName.model_name_number_complete(pre, p, post, z, d, r, n, w, hz, hd, hr):
  LN.mnn.nums_in(pre, p, post, String.append(p, String.append(z, String.append(d, r))), n, w, LN.mnn.on_app(p, z, d, r, n, w, hz, hd, hr))

# eukhe: the proof of LAW model_name_dash_plain
#
# PROOF: a text with no separator is kept from any state (LZ.mnz.plain).

import Base
import ../../bend/model_name.bend as M
import ../../laws/model_name.bend as ModelName
import ./base/dash.bend as LZ

def ModelName.model_name_dash_plain(s, h):
  LZ.mnz.plain(s, False{}, h)

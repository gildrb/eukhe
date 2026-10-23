# eukhe: the proof of LAW quirk_ladder_model_offers

import Base
import ../../laws/effort.bend as Effort
import ../base/fsmode.bend as LFsmode

def Effort.quirk_ladder_model_offers(r, LFsmode.explicit, rule, d):
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

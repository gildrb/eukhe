# eukhe: the proof of LAW quirk_ladder_model_offers

import Base
import ../../laws/effort/ladder.bend as EffortLadder
import ../base/fsmode.bend as LFsmode

def EffortLadder.quirk_ladder_model_offers(r, LFsmode.explicit, rule, d):
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

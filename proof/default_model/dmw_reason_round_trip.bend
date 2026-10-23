# eukhe: the proof of LAW dmw_reason_round_trip

import Base
import ../../bend/default_model.bend as Dm
import ../../laws/default_model.bend as DefaultModel

def DefaultModel.dmw_reason_round_trip(r, rest):
  match r:
    case Dm.NotInCatalog{}:
      {==}
    case Dm.NoCredentials{}:
      {==}
    case Dm.NotInScope{}:
      {==}

# eukhe: the proof of LAW dmw_reason_round_trip

import Base
import ../../bend/default_model.bend as Dm
import ../../LAWS.bend as Laws

def Laws.dmw_reason_round_trip(r, rest):
  match r:
    case Dm.NotInCatalog{}:
      {==}
    case Dm.NoCredentials{}:
      {==}
    case Dm.NotInScope{}:
      {==}

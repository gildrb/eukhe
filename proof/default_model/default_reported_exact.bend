# eukhe: the proof of LAW default_reported_exact

import Base
import ../../bend/default_model.bend as Dm
import ../../laws/default_model.bend as DefaultModel
import ./base.bend as LADefaultModel

def DefaultModel.default_reported_exact(x, s):
  match x:
    case Dm.In{saved, +cat, +key, out, next}:
      match saved:
        case Dm.NoDefault{}:
          {==}
        case Dm.Default{+m}:
          match s:
            case Dm.Session{run, notes}:
              %LADefaultModel.pdm.on_saved_spec(run) : {Bool.or(Dm.on_saved(run), Dm.listed(notes, Dm.K{m, Dm.why(cat, key)})) == Bool.or(_, DefaultModel.dms.listed(notes, Dm.K{m, DefaultModel.dms.why(cat, key)})) : Bool}
              %LADefaultModel.pdm.listed_spec(notes, Dm.K{m, DefaultModel.dms.why(cat, key)}) : {Bool.or(Dm.on_saved(run), Dm.listed(notes, Dm.K{m, Dm.why(cat, key)})) == Bool.or(Dm.on_saved(run), _) : Bool}
              %LADefaultModel.pdm.why_spec(cat, key) : {Bool.or(Dm.on_saved(run), Dm.listed(notes, Dm.K{m, Dm.why(cat, key)})) == Bool.or(Dm.on_saved(run), Dm.listed(notes, Dm.K{m, _})) : Bool}
              {==}

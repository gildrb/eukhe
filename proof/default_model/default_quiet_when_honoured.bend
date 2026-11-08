# eukhe: the proof of LAW default_quiet_when_honoured
#
# PROOF: case analysis over the request. Where the session runs on the
# saved default (a usable saved default) it has no notice; every other
# case opens it idle or on another model, which contradicts the premise
# (LA.pdm.idle_not_saved, LA.pdm.other_not_saved).

import Base
import ../../bend/default_model.bend as Dm
import ../../laws/default_model.bend as DefaultModel
import ./base.bend as LA

def DefaultModel.default_quiet_when_honoured(x, h):
  match x:
    case Dm.In{saved, cat, key, out, next}:
      match saved:
        case Dm.NoDefault{}:
          match next:
            case Dm.NoNext{}:
              {==}
            case Dm.Next{n}:
              {==}
        case Dm.Default{m}:
          match cat:
            case False{}:
              match next:
                case Dm.NoNext{}:
                  LA.pdm.idle_not_saved({[Dm.K{m, Dm.NotInCatalog{}}] == Nil{} : List<&2, Dm.Key>}, h)
                case Dm.Next{n}:
                  LA.pdm.other_not_saved({[Dm.K{m, Dm.NotInCatalog{}}] == Nil{} : List<&2, Dm.Key>}, n, h)
            case True{}:
              match key:
                case False{}:
                  LA.pdm.idle_not_saved({[Dm.K{m, Dm.NoCredentials{}}] == Nil{} : List<&2, Dm.Key>}, h)
                case True{}:
                  match out:
                    case False{}:
                      {==}
                    case True{}:
                      match next:
                        case Dm.NoNext{}:
                          LA.pdm.idle_not_saved({[Dm.K{m, Dm.NotInScope{}}] == Nil{} : List<&2, Dm.Key>}, h)
                        case Dm.Next{n}:
                          LA.pdm.other_not_saved({[Dm.K{m, Dm.NotInScope{}}] == Nil{} : List<&2, Dm.Key>}, n, h)

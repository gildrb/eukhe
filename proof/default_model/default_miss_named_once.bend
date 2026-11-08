# eukhe: the proof of LAW default_miss_named_once
#
# PROOF: case analysis over the facts, the chain's pick and the reason.
# Where r is the first check that fails, the session's one notice is
# K{m, r}; every other reason makes the premise False == True
# (LA.pdm.absurdF).

import Base
import ../../bend/default_model.bend as Dm
import ../../laws/default_model.bend as DefaultModel
import ./base.bend as LA

def DefaultModel.default_miss_named_once(m, cat, key, out, next, r, fails):
  match cat:
    case False{}:
      match next:
        case Dm.NoNext{}:
          match r:
            case Dm.NotInCatalog{}:
              {==}
            case Dm.NoCredentials{}:
              LA.pdm.absurdF({[Dm.K{m, Dm.NotInCatalog{}}] == [Dm.K{m, Dm.NoCredentials{}}] : List<&2, Dm.Key>}, fails)
            case Dm.NotInScope{}:
              LA.pdm.absurdF({[Dm.K{m, Dm.NotInCatalog{}}] == [Dm.K{m, Dm.NotInScope{}}] : List<&2, Dm.Key>}, fails)
        case Dm.Next{n}:
          match r:
            case Dm.NotInCatalog{}:
              {==}
            case Dm.NoCredentials{}:
              LA.pdm.absurdF({[Dm.K{m, Dm.NotInCatalog{}}] == [Dm.K{m, Dm.NoCredentials{}}] : List<&2, Dm.Key>}, fails)
            case Dm.NotInScope{}:
              LA.pdm.absurdF({[Dm.K{m, Dm.NotInCatalog{}}] == [Dm.K{m, Dm.NotInScope{}}] : List<&2, Dm.Key>}, fails)
    case True{}:
      match key:
        case False{}:
          match r:
            case Dm.NotInCatalog{}:
              LA.pdm.absurdF({[Dm.K{m, Dm.NoCredentials{}}] == [Dm.K{m, Dm.NotInCatalog{}}] : List<&2, Dm.Key>}, fails)
            case Dm.NoCredentials{}:
              {==}
            case Dm.NotInScope{}:
              LA.pdm.absurdF({[Dm.K{m, Dm.NoCredentials{}}] == [Dm.K{m, Dm.NotInScope{}}] : List<&2, Dm.Key>}, fails)
        case True{}:
          match out:
            case False{}:
              match r:
                case Dm.NotInCatalog{}:
                  LA.pdm.absurdF({Nil{} == [Dm.K{m, Dm.NotInCatalog{}}] : List<&2, Dm.Key>}, fails)
                case Dm.NoCredentials{}:
                  LA.pdm.absurdF({Nil{} == [Dm.K{m, Dm.NoCredentials{}}] : List<&2, Dm.Key>}, fails)
                case Dm.NotInScope{}:
                  LA.pdm.absurdF({Nil{} == [Dm.K{m, Dm.NotInScope{}}] : List<&2, Dm.Key>}, fails)
            case True{}:
              match next:
                case Dm.NoNext{}:
                  match r:
                    case Dm.NotInCatalog{}:
                      LA.pdm.absurdF({[Dm.K{m, Dm.NotInScope{}}] == [Dm.K{m, Dm.NotInCatalog{}}] : List<&2, Dm.Key>}, fails)
                    case Dm.NoCredentials{}:
                      LA.pdm.absurdF({[Dm.K{m, Dm.NotInScope{}}] == [Dm.K{m, Dm.NoCredentials{}}] : List<&2, Dm.Key>}, fails)
                    case Dm.NotInScope{}:
                      {==}
                case Dm.Next{n}:
                  match r:
                    case Dm.NotInCatalog{}:
                      LA.pdm.absurdF({[Dm.K{m, Dm.NotInScope{}}] == [Dm.K{m, Dm.NotInCatalog{}}] : List<&2, Dm.Key>}, fails)
                    case Dm.NoCredentials{}:
                      LA.pdm.absurdF({[Dm.K{m, Dm.NotInScope{}}] == [Dm.K{m, Dm.NoCredentials{}}] : List<&2, Dm.Key>}, fails)
                    case Dm.NotInScope{}:
                      {==}

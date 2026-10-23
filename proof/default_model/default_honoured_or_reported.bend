# eukhe: the proof of LAW default_honoured_or_reported

import Base
import ../../bend/default_model.bend as Dm
import ../../LAWS.bend as Laws

# the one notice of the key K{m, r} names K{m, r}
def pdm.listed_self(m: Nat, r: Dm.Reason) -> {Dm.listed([Dm.K{m, r}], Dm.K{m, r}) == True{} : Bool}:
  match m:
    case 0n:
      match r:
        case Dm.NotInCatalog{}:
          {==}
        case Dm.NoCredentials{}:
          {==}
        case Dm.NotInScope{}:
          {==}
    case 1n+p:
      pdm.listed_self(p, r)

# Laws
# ----

# LAW default_honoured_or_reported: the session runs on the saved default,
# or its notices name the saved default with the reason it did not run
def pdm.default_honoured_or_reported(x: Dm.In) -> {Dm.reported(x, Dm.open(Dm.resolve(x))) == True{} : Bool}:
  match x:
    case Dm.In{saved, cat, key, out, next}:
      match saved:
        case Dm.NoDefault{}:
          {==}
        case Dm.Default{m}:
          match cat:
            case False{}:
              match next:
                case Dm.NoNext{}:
                  pdm.listed_self(m, Dm.NotInCatalog{})
                case Dm.Next{n}:
                  pdm.listed_self(m, Dm.NotInCatalog{})
            case True{}:
              match key:
                case False{}:
                  pdm.listed_self(m, Dm.NoCredentials{})
                case True{}:
                  match out:
                    case False{}:
                      {==}
                    case True{}:
                      match next:
                        case Dm.NoNext{}:
                          pdm.listed_self(m, Dm.NotInScope{})
                        case Dm.Next{n}:
                          pdm.listed_self(m, Dm.NotInScope{})

# The saved default model
# -----------------------
# The proofs are in PROOF.bend section default_model.

def pcf.default_honoured_or_reported(x: Dm.In) -> {Dm.reported(x, Dm.open(Dm.resolve(x))) == True{} : Bool}:
  pdm.default_honoured_or_reported(x)

def Laws.default_honoured_or_reported(x):
  pcf.default_honoured_or_reported(x)

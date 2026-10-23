# eukhe: the proof of LAW default_quiet_when_honoured

import Base
import ../../bend/default_model.bend as Dm
import ../../LAWS.bend as Laws

# ---- default_model ----

# proof_default_model: lemmas for the laws that the saved default model
# runs or is reported (bend/default_model.bend). A resolution is finite
# case analysis over the saved default, the catalog, the credentials, the
# scope and the chain's next pick. In each case the session runs on the
# saved default with no notice, or its one notice is the key of the saved
# default and the first check it fails. That key is on the notice list
# because a key equals itself (`pdm.listed_self`, an induction on the
# model number).
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters).

# Logic
# -----

def pdm.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pdm.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pdm.BD(_, A, Unit)
  Unit{}

# LAW default_quiet_when_honoured: a session that runs on the saved
# default has no notice
def pdm.default_quiet_when_honoured(x: Dm.In, h: {Dm.on_saved(Dm.Session.run(Dm.open(Dm.resolve(x)))) == True{} : Bool}) -> {Dm.none(Dm.Session.notes(Dm.open(Dm.resolve(x)))) == True{} : Bool}:
  match x:
    case Dm.In{saved, cat, key, out, next}:
      match saved:
        case Dm.NoDefault{}:
          match next:
            case Dm.NoNext{}:
              pdm.absurdF({True{} == True{} : Bool}, h)
            case Dm.Next{n}:
              pdm.absurdF({True{} == True{} : Bool}, h)
        case Dm.Default{m}:
          match cat:
            case False{}:
              match next:
                case Dm.NoNext{}:
                  pdm.absurdF({False{} == True{} : Bool}, h)
                case Dm.Next{n}:
                  pdm.absurdF({False{} == True{} : Bool}, h)
            case True{}:
              match key:
                case False{}:
                  pdm.absurdF({False{} == True{} : Bool}, h)
                case True{}:
                  match out:
                    case False{}:
                      {==}
                    case True{}:
                      match next:
                        case Dm.NoNext{}:
                          pdm.absurdF({False{} == True{} : Bool}, h)
                        case Dm.Next{n}:
                          pdm.absurdF({False{} == True{} : Bool}, h)

def pcf.default_quiet_when_honoured(x: Dm.In, h: {Dm.on_saved(Dm.Session.run(Dm.open(Dm.resolve(x)))) == True{} : Bool}) -> {Dm.none(Dm.Session.notes(Dm.open(Dm.resolve(x)))) == True{} : Bool}:
  pdm.default_quiet_when_honoured(x, h)

def Laws.default_quiet_when_honoured(x, h):
  pcf.default_quiet_when_honoured(x, h)

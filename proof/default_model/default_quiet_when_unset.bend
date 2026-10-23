# eukhe: the proof of LAW default_quiet_when_unset

import Base
import ../../bend/default_model.bend as Dm
import ../../LAWS.bend as Laws

# LAW default_quiet_when_unset: with no saved default the session has no
# notice
def pdm.default_quiet_when_unset(cat: Bool, key: Bool, out: Bool, next: Dm.Next) -> {Dm.Session.notes(Dm.open(Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, next}))) == Nil{} : List<&2, Dm.Key>}:
  match next:
    case Dm.NoNext{}:
      {==}
    case Dm.Next{n}:
      {==}

def pcf.default_quiet_when_unset(cat: Bool, key: Bool, out: Bool, next: Dm.Next) -> {Dm.Session.notes(Dm.open(Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, next}))) == Nil{} : List<&2, Dm.Key>}:
  pdm.default_quiet_when_unset(cat, key, out, next)

def Laws.default_quiet_when_unset(cat, key, out, next):
  pcf.default_quiet_when_unset(cat, key, out, next)

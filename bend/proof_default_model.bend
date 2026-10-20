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

import Base
import ./default_model.bend as Dm

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

# LAW default_quiet_when_unset: with no saved default the session has no
# notice
def pdm.default_quiet_when_unset(cat: Bool, key: Bool, out: Bool, next: Dm.Next) -> {Dm.Session.notes(Dm.open(Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, next}))) == Nil{} : List<&2, Dm.Key>}:
  match next:
    case Dm.NoNext{}:
      {==}
    case Dm.Next{n}:
      {==}

# LAW default_unkeyed_never_moves: a saved default whose provider has no
# credentials opens the session with no model; no other provider runs
def pdm.default_unkeyed_never_moves(m: Nat, out: Bool, next: Dm.Next) -> {Dm.Session.run(Dm.open(Dm.resolve(Dm.In{Dm.Default{m}, True{}, False{}, out, next}))) == Dm.Idle{} : Dm.Run}:
  {==}

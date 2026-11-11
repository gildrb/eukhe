# eukhe: the proof of LAW effort_unset_stays
# By induction on the actions: a switch or a step of an unset session
# leaves it unset (a switch takes the new model), and a set is excluded.

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA

def us.go(acts: List<&2, Ef.Act>, mo: Maybe<&2, Ef.Mdl>, noset: {Effort.effort_no_set(acts) == True{} : Bool}) -> {Ef.shown(Ef.run(acts, Ef.Sess{mo, None{}})) == Ef.Default{} : Ef.Shown}:
  match acts:
    case Nil{}:
      {==}
    case a <> rest:
      match a:
        case Ef.Switch{m}:
          us.go(rest, Some{m}, noset)
        case Ef.SetLevel{l}:
          LA.pe.absurdF({Ef.shown(Ef.run(rest, Ef.act(Ef.SetLevel{l}, Ef.Sess{mo, None{}}))) == Ef.Default{} : Ef.Shown}, noset)
        case Ef.Step{d}:
          us.go(rest, mo, noset)

def Effort.effort_unset_stays(mo, acts, noset):
  us.go(acts, mo, noset)

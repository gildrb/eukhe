# eukhe: the proof of LAW cell_runs_only_within_or_approved

import Base
import ../../bend/runners.bend as Ru
import ../../LAWS.bend as Laws
import ./base.bend as LA

# The cell gate
# -------------

def pr.go_only(free: Bool, a: Ru.Asker, ran: {Ru.ran(Ru.cell.go(free, a)) == True{} : Bool}) -> {Bool.or(free, Ru.Asker.yes(a)) == True{} : Bool}:
  match free:
    case True{}:
      {==}
    case False{}:
      match a:
        case Ru.NoClient{}:
          LA.pr.absurdF({False{} == True{} : Bool}, ran)
        case Ru.Silent{}:
          LA.pr.absurdF({False{} == True{} : Bool}, ran)
        case Ru.Says{y}:
          match y:
            case True{}:
              {==}
            case False{}:
              LA.pr.absurdF({False{} == True{} : Bool}, ran)

def pr.only(+caps: List<&2, Nat>, +auto: List<&2, Nat>, +a: Ru.Asker, ran: {Ru.ran(Ru.cell(caps, auto, a)) == True{} : Bool}) -> {Bool.or(Ru.within(caps, auto), Ru.Asker.yes(a)) == True{} : Bool}:
  pr.go_only(Ru.within(caps, auto), a, ran)

def Laws.cell_runs_only_within_or_approved(caps, auto, a, ran):
  pr.only(caps, auto, a, ran)

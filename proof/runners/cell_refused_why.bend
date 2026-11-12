# eukhe: the proof of LAW cell_refused_why
#
# PROOF: case on whether the caps are within the auto set and the asker: a call that did not run is Denied exactly on a no, Unanswered otherwise; the calls that ran contradict stopped.

import Base
import ../../bend/runners.bend as Ru
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/runners.bend as Runners
import ../base/staging.bend as LStg

def crw.go(b: Bool, a: Ru.Asker, stopped: {Ru.ran(Ru.cell.go(b, a)) == False{} : Bool}) -> {Runners.ru_denied(Ru.Out.end(Ru.cell.go(b, a))) == Runners.ru_says_no(a) : Bool}:
  match b:
    case True{}:
      LStg.stg.absurd({Runners.ru_denied(Ru.Ran{Ru.Auto{}}) == Runners.ru_says_no(a) : Bool}, stopped)
    case False{}:
      match a:
        case Ru.NoClient{}:
          {==}
        case Ru.Silent{}:
          {==}
        case Ru.Says{y}:
          match y:
            case True{}:
              LStg.stg.absurd({False{} == False{} : Bool}, stopped)
            case False{}:
              {==}

def Runners.cell_refused_why(caps, auto, a, stopped):
  crw.go(Ru.within(caps, auto), a, stopped)

# eukhe: the proof of LAW cell_ran_how
#
# PROOF: case on whether the caps are within the auto set and the asker: a call that ran is Auto within it and Approved outside; the other cases did not run (ran contradicts them).

import Base
import ../../bend/runners.bend as Ru
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/runners.bend as Runners
import ../base/staging.bend as LStg

def crh.go(b: Bool, a: Ru.Asker, ran: {Ru.ran(Ru.cell.go(b, a)) == True{} : Bool}) -> {Runners.ru_auto(Ru.Out.end(Ru.cell.go(b, a))) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match a:
        case Ru.NoClient{}:
          LStg.stg.absurdF({False{} == False{} : Bool}, ran)
        case Ru.Silent{}:
          LStg.stg.absurdF({False{} == False{} : Bool}, ran)
        case Ru.Says{y}:
          match y:
            case True{}:
              {==}
            case False{}:
              LStg.stg.absurdF({False{} == False{} : Bool}, ran)

def Runners.cell_ran_how(caps, auto, a, ran):
  crh.go(Ru.within(caps, auto), a, ran)

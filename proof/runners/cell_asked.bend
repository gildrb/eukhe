# eukhe: the proof of LAW cell_asked
#
# PROOF: the call is the code's cell.go on whether the caps are within the auto set; case on that and the asker: each computes.

import Base
import ../../bend/runners.bend as Ru
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/runners.bend as Runners
import ../base/staging.bend as LStg

def cla.go(b: Bool, a: Ru.Asker) -> {Runners.ru_asked(Ru.cell.go(b, a)) == Bool.and(Bool.not(b), Runners.ru_client(a)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match a:
        case Ru.NoClient{}:
          {==}
        case Ru.Silent{}:
          {==}
        case Ru.Says{y}:
          match y:
            case True{}:
              {==}
            case False{}:
              {==}

def Runners.cell_asked(caps, auto, a):
  cla.go(Ru.within(caps, auto), a)

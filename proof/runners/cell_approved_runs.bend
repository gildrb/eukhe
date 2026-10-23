# eukhe: the proof of LAW cell_approved_runs

import Base
import ../../bend/runners.bend as Ru
import ../../laws/runners.bend as Runners

def pr.approved(+caps: List<&2, Nat>, +auto: List<&2, Nat>, held: {Ru.within(caps, auto) == False{} : Bool}) -> {Ru.cell(caps, auto, Ru.Says{True{}}) == Ru.Out{True{}, Ru.Ran{Ru.Approved{}}} : Ru.Out}:
  %Equal.sym(Bool, Ru.within(caps, auto), False{}, held) : {Ru.cell.go(_, Ru.Says{True{}}) == Ru.Out{True{}, Ru.Ran{Ru.Approved{}}} : Ru.Out}
  {==}

def Runners.cell_approved_runs(caps, auto, held):
  pr.approved(caps, auto, held)

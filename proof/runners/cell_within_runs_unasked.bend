# eukhe: the proof of LAW cell_within_runs_unasked

import Base
import ../../bend/runners.bend as Ru
import ../../LAWS.bend as Laws

def pr.unasked(+caps: List<&2, Nat>, +auto: List<&2, Nat>, a: Ru.Asker, free: {Ru.within(caps, auto) == True{} : Bool}) -> {Ru.cell(caps, auto, a) == Ru.Out{False{}, Ru.Ran{Ru.Auto{}}} : Ru.Out}:
  %Equal.sym(Bool, Ru.within(caps, auto), True{}, free) : {Ru.cell.go(_, a) == Ru.Out{False{}, Ru.Ran{Ru.Auto{}}} : Ru.Out}
  {==}

def Laws.cell_within_runs_unasked(caps, auto, a, free):
  pr.unasked(caps, auto, a, free)

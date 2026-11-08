# eukhe: the proof of LAW runners_cell_spec
# The model's within is the spec's (runners_within_spec); the rest by cases.

import Base
import ../../bend/runners.bend as Ru
import ../../laws/runners.bend as Runners
import ./runners_within_spec.bend as PRunnersWithinSpec

def ruc.go(free: Bool, a: Ru.Asker) -> {Ru.cell.go(free, a) == Runners.ru_cell(free, a) : Ru.Out}:
  match free:
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

def Runners.runners_cell_spec(caps, auto, a):
  %Runners.runners_within_spec(caps, auto) : {Ru.cell(caps, auto, a) == Runners.ru_cell(_, a) : Ru.Out}
  ruc.go(Ru.within(caps, auto), a)

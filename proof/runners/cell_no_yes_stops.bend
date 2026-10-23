# eukhe: the proof of LAW cell_no_yes_stops

import Base
import ../../bend/runners.bend as Ru
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pr.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : LA.pr.BD(_, Unit, A)
  Unit{}

def pr.no_yes(a: Ru.Asker, no: {Ru.Asker.yes(a) == False{} : Bool}) -> {Ru.ran(Ru.cell.go(False{}, a)) == False{} : Bool}:
  match a:
    case Ru.NoClient{}:
      {==}
    case Ru.Silent{}:
      {==}
    case Ru.Says{y}:
      match y:
        case True{}:
          pr.absurdT({True{} == False{} : Bool}, no)
        case False{}:
          {==}

def pr.stops(+caps: List<&2, Nat>, +auto: List<&2, Nat>, +a: Ru.Asker, held: {Ru.within(caps, auto) == False{} : Bool}, no: {Ru.Asker.yes(a) == False{} : Bool}) -> {Ru.ran(Ru.cell(caps, auto, a)) == False{} : Bool}:
  %Equal.sym(Bool, Ru.within(caps, auto), False{}, held) : {Ru.ran(Ru.cell.go(_, a)) == False{} : Bool}
  pr.no_yes(a, no)

def Laws.cell_no_yes_stops(caps, auto, a, held, no):
  pr.stops(caps, auto, a, held, no)

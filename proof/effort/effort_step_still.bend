# eukhe: the proof of LAW effort_step_still
# Case by case on the model and the stored level.

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA

def sl.go(mo: Maybe<&2, Ef.Mdl>, st: Maybe<&2, Ef.Lv>, +d: Ef.Dir, idle: {Bool.or(Maybe.is_none(&2, Ef.Mdl, mo), Maybe.is_none(&2, Ef.Lv, st)) == True{} : Bool}) -> {Ef.act(Ef.Step{d}, Ef.Sess{mo, st}) == Ef.Sess{mo, st} : Ef.Sess}:
  match mo:
    case None{}:
      match st:
        case None{}:
          {==}
        case Some{l}:
          {==}
    case Some{m}:
      match st:
        case None{}:
          {==}
        case Some{l}:
          LA.pe.absurdF({Ef.act(Ef.Step{d}, Ef.Sess{Some{m}, Some{l}}) == Ef.Sess{Some{m}, Some{l}} : Ef.Sess}, idle)

def Effort.effort_step_still(mo, st, d, idle):
  sl.go(mo, st, d, idle)

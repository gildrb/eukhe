# eukhe: the proof of LAW effort_shown_is_sent

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort.bend as Effort
import ./base.bend as LA

def pe.fix_shown(t: Ef.Sess, f: LA.pe.Fixed(t)) -> {Ef.shown(t) == Ef.Level{Ef.sent(t)} : Ef.Shown}:
  match t:
    case Ef.Sess{+mo, st}:
      match st:
        case None{}:
          LA.pe.void({Ef.shown(Ef.Sess{mo, None{}}) == Ef.Level{Ef.sent(Ef.Sess{mo, None{}})} : Ef.Shown}, f)
        case Some{+l}:
          {==}

def pe.effort_shown_is_sent(+s: Ef.Sess, +dflt: Ef.Lv, +acts: List<&2, Ef.Act>) -> {Ef.shown(Ef.run(acts, Ef.open(s, dflt))) == Ef.Level{Ef.sent(Ef.run(acts, Ef.open(s, dflt)))} : Ef.Shown}:
  pe.fix_shown(Ef.run(acts, Ef.open(s, dflt)), LA.pe.run_fix(acts, Ef.open(s, dflt), LA.pe.open_fix(s, dflt)))

def Effort.effort_shown_is_sent(s, dflt, acts):
  pe.effort_shown_is_sent(s, dflt, acts)

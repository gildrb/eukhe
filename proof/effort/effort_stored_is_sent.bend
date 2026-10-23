# eukhe: the proof of LAW effort_stored_is_sent

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort.bend as Effort
import ./base.bend as LA

def pe.fix_sent(t: Ef.Sess, f: LA.pe.Fixed(t)) -> {Ef.Sess.stored(t) == Some{Ef.sent(t)} : Maybe<&2, Ef.Lv>}:
  match t:
    case Ef.Sess{+mo, st}:
      match st:
        case None{}:
          LA.pe.void({Ef.Sess.stored(Ef.Sess{mo, None{}}) == Some{Ef.sent(Ef.Sess{mo, None{}})} : Maybe<&2, Ef.Lv>}, f)
        case Some{+l}:
          Equal.cong(Ef.Lv, Maybe<&2, Ef.Lv>, v => Some{v}, l, Ef.fit(mo, l), Equal.sym(Ef.Lv, Ef.fit(mo, l), l, f))

def pe.effort_stored_is_sent(+s: Ef.Sess, +dflt: Ef.Lv, +acts: List<&2, Ef.Act>) -> {Ef.Sess.stored(Ef.run(acts, Ef.open(s, dflt))) == Some{Ef.sent(Ef.run(acts, Ef.open(s, dflt)))} : Maybe<&2, Ef.Lv>}:
  pe.fix_sent(Ef.run(acts, Ef.open(s, dflt)), LA.pe.run_fix(acts, Ef.open(s, dflt), LA.pe.open_fix(s, dflt)))

def Effort.effort_stored_is_sent(s, dflt, acts):
  pe.effort_stored_is_sent(s, dflt, acts)

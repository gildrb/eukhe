# eukhe: the proof of LAW effort_settle_offered

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort.bend as Effort
import ./base.bend as LA

def pe.effort_settle_offered(+m: Ef.Mdl, +st: Maybe<&2, Ef.Lv>, +dflt: Ef.Lv, +k: Ef.Lv, ne: {Ef.empty(Ef.offered(m)) == False{} : Bool}, settled: {Ef.Sess.stored(Ef.open(Ef.Sess{Some{m}, st}, dflt)) == Some{k} : Maybe<&2, Ef.Lv>}) -> {Ef.has(Ef.offered(m), k) == True{} : Bool}:
  +x = Maybe.default(&2, Ef.Lv, st, dflt)
  +e = Equal.cong(Maybe<&2, Ef.Lv>, Ef.Lv, v => Maybe.default(&2, Ef.Lv, v, Ef.Off{}), Some{Ef.clamp(m, x)}, Some{k}, settled)
  %e : {Ef.has(Ef.offered(m), _) == True{} : Bool}
  LA.pe.clamp_in(Ef.offered(m), x, ne)

def Effort.effort_settle_offered(m, st, dflt, k, ne, settled):
  pe.effort_settle_offered(m, st, dflt, k, ne, settled)

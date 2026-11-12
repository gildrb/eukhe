# eukhe: the proof of LAW effort_set_fits
# Stored or not, a set stores the fit of the requested level (SF.sf.fit).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA
import ./effort_open_fits.bend as SF

def ss.go(+mo: Maybe<&2, Ef.Mdl>, st: Maybe<&2, Ef.Lv>, +k: Ef.Lv, +j: Ef.Lv, fit: {Effort.effort_fits(mo, k, j) == True{} : Bool}) -> {Ef.act(Ef.SetLevel{k}, Ef.Sess{mo, st}) == Ef.Sess{mo, Some{j}} : Ef.Sess}:
  match st:
    case None{}:
      Equal.cong(Ef.Lv, Ef.Sess, v => SF.sf.with(mo, v), Ef.fit(mo, k), j, SF.sf.fit(mo, k, j, fit))
    case Some{l}:
      Equal.cong(Ef.Lv, Ef.Sess, v => SF.sf.with(mo, v), Ef.fit(mo, k), j, SF.sf.fit(mo, k, j, fit))

def Effort.effort_set_fits(mo, st, k, j, fit):
  ss.go(mo, st, k, j, fit)

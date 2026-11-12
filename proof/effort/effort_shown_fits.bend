# eukhe: the proof of LAW effort_shown_fits
# A stored level shows its fit (SF.sf.fit).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA
import ./effort_open_fits.bend as SF

def Effort.effort_shown_fits(mo, l, k, fit):
  Equal.cong(Ef.Lv, Ef.Shown, v => Ef.Level{v}, Ef.fit(mo, l), k, SF.sf.fit(mo, l, k, fit))

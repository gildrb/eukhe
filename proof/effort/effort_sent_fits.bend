# eukhe: the proof of LAW effort_sent_fits
# The runtime sends the fit of the stored level, else of off (SF.sf.fit).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA
import ./effort_open_fits.bend as SF

def Effort.effort_sent_fits(mo, st, k, fit):
  SF.sf.fit(mo, Maybe.default(&2, Ef.Lv, st, Ef.Off{}), k, fit)

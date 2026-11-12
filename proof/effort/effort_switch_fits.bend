# eukhe: the proof of LAW effort_switch_fits
# No stored level stays none; a stored one is clamped to the new model,
# its fit (SF.sf.fit).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA
import ./effort_open_fits.bend as SF

def sw.go(+m: Ef.Mdl, +mo: Maybe<&2, Ef.Mdl>, st: Maybe<&2, Ef.Lv>, r: Maybe<&2, Ef.Lv>, fit: {Effort.effort_fits_m(Some{m}, st, r) == True{} : Bool}) -> {Ef.act(Ef.Switch{m}, Ef.Sess{mo, st}) == Ef.Sess{Some{m}, r} : Ef.Sess}:
  match st:
    case None{}:
      match r:
        case None{}:
          {==}
        case Some{k}:
          LA.pe.absurdF({Ef.Sess{Some{m}, None{}} == Ef.Sess{Some{m}, Some{k}} : Ef.Sess}, fit)
    case Some{+l}:
      match r:
        case None{}:
          LA.pe.absurdF({Ef.Sess{Some{m}, Some{Ef.clamp(m, l)}} == Ef.Sess{Some{m}, None{}} : Ef.Sess}, fit)
        case Some{+k}:
          Equal.cong(Ef.Lv, Ef.Sess, v => SF.sf.with(Some{m}, v), Ef.clamp(m, l), k, SF.sf.fit(Some{m}, l, k, fit))

def Effort.effort_switch_fits(m, mo, st, r, fit):
  sw.go(m, mo, st, r, fit)

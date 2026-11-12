# eukhe: the proof of LAW effort_step_turns
# The step stores the clamp of the level the cycle gives, which is that
# level: it is offered (CM.cm.cycle_in) and the clamp keeps an offered
# level (LA.pe.clamp_keep); with none it keeps the stored level.

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA
import ./effort_cycle_moves.bend as CM
import ./effort_open_fits.bend as SF

def st.set(+m: Ef.Mdl, +l: Ef.Lv, d: Ef.Dir, r: Maybe<&2, Ef.Lv>, e: {Ef.cycle(m, l, d) == r : Maybe<&2, Ef.Lv>}) -> {Ef.step.set(m, r, l) == Maybe.default(&2, Ef.Lv, r, l) : Ef.Lv}:
  match r:
    case None{}:
      {==}
    case Some{+k}:
      LA.pe.clamp_keep(Ef.offered(m), k, CM.cm.cycle_in(m, l, d, k, e))

def Effort.effort_step_turns(m, l, d):
  +c = Ef.cycle(m, l, d)
  Equal.cong(Ef.Lv, Ef.Sess, v => SF.sf.with(Some{m}, v), Ef.step.set(m, c, l), Maybe.default(&2, Ef.Lv, c, l), st.set(m, l, d, c, {==}))

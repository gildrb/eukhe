# eukhe: the proof of LAW tui_color_ffi_ramp
# The request reads back whole (LA.tcf.dec); the range check is the
# premise; the reply is the spec's list of the model's rungs (LA.tcf.rungs).

import Base
import ../../bend/ffi_tui_color.bend as FTC
import ../../bend/tui_color.bend as TC
import ../../bend/wire.bend as Wr
import ../../laws/tui_color.bend as TuiColor
import ./base.bend as LA

def TuiColor.tui_color_ffi_ramp(lo, hi, n, fit, in):
  match lo hi:
    case TC.Px{+lr, +lg, +lb} TC.Px{+hr, +hg, +hb}:
      +q = {FTC.QRamp{TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n} : FTC.Req}
      +rhs = TuiColor.spell_rungs(TC.ramp(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n))
      %Equal.sym(Wr.Dec<FTC.Req>, FTC.get_req(TuiColor.spell_req(q, "")), Wr.Got{q, ""}, LA.tcf.dec(q, "", fit)) : {FTC.run(_) == rhs : String}
      %Equal.sym(Bool, TuiColor.ramp_in(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n), True{}, in) : {FTC.answer.ramp(_, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n) == rhs : String}
      LA.tcf.rungs(TC.ramp(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n))

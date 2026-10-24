# eukhe: the proof of LAW tui_color_ffi_ramp_range
# The request reads back whole (LA.tcf.dec); the range check fails (the
# premise), and the reply is the range error.

import Base
import ../../bend/ffi_tui_color.bend as FTC
import ../../bend/tui_color.bend as TC
import ../../bend/wire.bend as Wr
import ../../laws/tui_color.bend as TuiColor
import ./base.bend as LA

def TuiColor.tui_color_ffi_ramp_range(lo, hi, n, fit, out):
  match lo hi:
    case TC.Px{+lr, +lg, +lb} TC.Px{+hr, +hg, +hb}:
      +q = {FTC.QRamp{TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n} : FTC.Req}
      %Equal.sym(Wr.Dec<FTC.Req>, FTC.get_req(TuiColor.spell_req(q, "")), Wr.Got{q, ""}, LA.tcf.dec(q, "", fit)) : {FTC.run(_) == TuiColor.range_err() : String}
      %Equal.sym(Bool, TuiColor.ramp_in(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n), False{}, out) : {FTC.answer.ramp(_, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n) == TuiColor.range_err() : String}
      {==}

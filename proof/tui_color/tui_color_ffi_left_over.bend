# eukhe: the proof of LAW tui_color_ffi_left_over
# The request reads back with the left-over input as its rest
# (LA.tcf.dec); a rest that is not empty fails the end check.

import Base
import ../../bend/ffi_tui_color.bend as FTC
import ../../bend/wire.bend as Wr
import ../../laws/tui_color.bend as TuiColor
import ./base.bend as LA

def TuiColor.tui_color_ffi_left_over(q, fit, c, rest):
  +r = {SCon{c, rest} : String}
  %Equal.sym(Wr.Dec<FTC.Req>, FTC.get_req(TuiColor.spell_req(q, r)), Wr.Got{q, r}, LA.tcf.dec(q, r, fit)) : {FTC.run(_) == TuiColor.malformed_err() : String}
  {==}

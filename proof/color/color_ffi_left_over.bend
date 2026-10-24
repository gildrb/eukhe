# eukhe: the proof of LAW color_ffi_left_over
# The request reads back whole and leaves the input after it
# (LCo.ce.list_rt); the entry's end check finds that input and refuses.

import Base
import ../../bend/color.bend as Co
import ../../bend/ffi_color.bend as FCo
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/color.bend as Color
import ../base/logic/bool.bend as LLogicBool
import ./base.bend as LCo

def cl.quantize(+cs: List<&2, Co.Rgb>, +fits: {Color.co_fits(FCo.Quantize{cs}) == True{} : Bool}, c: Char, x: String) -> {FCo.ffi(Color.co_spell_req(FCo.Quantize{cs}, SCon{c, x})) == Color.co_refused() : String}:
  +hl = LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  +hr = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  %LCo.ce.list_rt(cs, SCon{c, x}, hl, hr) : {FCo.run(FCo.get_quantize(_)) == Color.co_refused() : String}
  {==}

def cl.lights(+cs: List<&2, Co.Rgb>, +fits: {Color.co_fits(FCo.Lights{cs}) == True{} : Bool}, c: Char, x: String) -> {FCo.ffi(Color.co_spell_req(FCo.Lights{cs}, SCon{c, x})) == Color.co_refused() : String}:
  +hl = LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  +hr = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  %LCo.ce.list_rt(cs, SCon{c, x}, hl, hr) : {FCo.run(FCo.get_lights(_)) == Color.co_refused() : String}
  {==}

def Color.color_ffi_left_over(r, fits, c, x):
  match r:
    case FCo.Quantize{cs}:
      cl.quantize(cs, fits, c, x)
    case FCo.Lights{cs}:
      cl.lights(cs, fits, c, x)
    case FCo.Table{}:
      {==}

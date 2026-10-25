# eukhe: the proof of LAW color_ffi_answers
# The colors of a request read back one by one (LCo.ce.list_rt: the
# wire's round trips, each channel within 255), and the reply writers
# write what the laws spell (LCo.ce.idxs, LCo.ce.lights_w, LCo.ce.table).

import Base
import ../../bend/color.bend as Co
import ../../bend/ffi_color.bend as FCo
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/color.bend as Color
import ../base/logic/bool.bend as LLogicBool
import ./base.bend as LCo

def ca.quantize(+cs: List<&2, Co.Rgb>, +fits: {Color.co_fits(FCo.Quantize{cs}) == True{} : Bool}) -> {FCo.ffi(Color.co_spell_req(FCo.Quantize{cs}, "")) == Color.co_spell_answer(FCo.Quantize{cs}) : String}:
  +hl = LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  +hr = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  %LCo.ce.list_rt(cs, "", hl, hr) : {FCo.run(FCo.get_quantize(_)) == Color.co_spell_answer(FCo.Quantize{cs}) : String}
  %LCo.ce.idxs(cs, "") : {Wr.put_nat(List.length(&2, Co.Rgb, cs), FCo.put_idxs.items(cs, "")) == Wr.put_nat(List.length(&2, Co.Rgb, cs), _) : String}
  {==}

def ca.lights(+cs: List<&2, Co.Rgb>, +fits: {Color.co_fits(FCo.Lights{cs}) == True{} : Bool}) -> {FCo.ffi(Color.co_spell_req(FCo.Lights{cs}, "")) == Color.co_spell_answer(FCo.Lights{cs}) : String}:
  +hl = LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  +hr = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  %LCo.ce.list_rt(cs, "", hl, hr) : {FCo.run(FCo.get_lights(_)) == Color.co_spell_answer(FCo.Lights{cs}) : String}
  %LCo.ce.lights_w(cs, "") : {Wr.put_nat(List.length(&2, Co.Rgb, cs), FCo.put_lights.items(cs, "")) == Wr.put_nat(List.length(&2, Co.Rgb, cs), _) : String}
  {==}

def ca.table() -> {FCo.ffi(Color.co_spell_req(FCo.Table{}, "")) == Color.co_spell_answer(FCo.Table{}) : String}:
  %LCo.ce.table(256n, 0, "") : {Wr.put_nat(256n, FCo.put_table(256n, 0, "")) == Wr.put_nat(256n, _) : String}
  {==}

def Color.color_ffi_answers(r, fits):
  match r:
    case FCo.Quantize{cs}:
      ca.quantize(cs, fits)
    case FCo.Lights{cs}:
      ca.lights(cs, fits)
    case FCo.Table{}:
      ca.table()

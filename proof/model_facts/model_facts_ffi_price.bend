# eukhe: the proof of LAW model_facts_ffi_price
# The count, every row (LAMF.mfb.go), the model and the tier read back;
# the reply encodes the model's price as the spec does (LAMF.mfb.mnat).

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/model_facts.bend as ModelFacts
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ./base.bend as LAMF

def mfp.tail(+rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat, +hm: {LawsBase.wire_fits(m) == True{} : Bool}, +ht: {LawsBase.wire_fits(t) == True{} : Bool}) -> {FMF.run(FMF.get_price.m(rows, Wr.get_nat(Wr.put_nat(m, Wr.put_nat(t, ""))))) == ModelFacts.mf.mnat(Fx.price(rows, m, t), "") : String}:
  %LWire.pw6.nat(m, Wr.put_nat(t, ""), hm) : {FMF.run(FMF.get_price.m(rows, _)) == ModelFacts.mf.mnat(Fx.price(rows, m, t), "") : String}
  %LWire.pw6.nat(t, "", ht) : {FMF.run(FMF.get_price.t(rows, m, _)) == ModelFacts.mf.mnat(Fx.price(rows, m, t), "") : String}
  LAMF.mfb.mnat(Fx.price(rows, m, t))

def mfp.rows(rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat, hl: {LawsBase.wire_fits(List.length(&2, Fx.PRow, rows)) == True{} : Bool}, +hrows: {ModelFacts.mf.rows_fit(rows) == True{} : Bool}, +hm: {LawsBase.wire_fits(m) == True{} : Bool}, +ht: {LawsBase.wire_fits(t) == True{} : Bool}) -> {FMF.ffi(ModelFacts.spell_price(rows, m, t)) == ModelFacts.mf.mnat(Fx.price(rows, m, t), "") : String}:
  match rows:
    case Nil{}:
      mfp.tail(Nil{}, m, t, hm, ht)
    case Fx.PRow{+rm, +rt, +rk} <> +more:
      +tail = Wr.put_nat(m, Wr.put_nat(t, ""))
      +all = {Fx.PRow{rm, rt, rk} <> more : List<&2, Fx.PRow>}
      %LWire.pw6.nat(List.length(&2, Fx.PRow, all), ModelFacts.mf.items(all, tail), hl) : {FMF.run(FMF.get_price(FMF.get_rows(_))) == ModelFacts.mf.mnat(Fx.price(all, m, t), "") : String}
      +h1 = LLogicBool.wr_and_l(LawsBase.wire_mfits(rm), Bool.and(LawsBase.wire_fits(rt), Bool.and(LawsBase.wire_fits(rk), ModelFacts.mf.rows_fit(more))), hrows)
      +g1 = LLogicBool.wr_and_r(LawsBase.wire_mfits(rm), Bool.and(LawsBase.wire_fits(rt), Bool.and(LawsBase.wire_fits(rk), ModelFacts.mf.rows_fit(more))), hrows)
      +h2 = LLogicBool.wr_and_l(LawsBase.wire_fits(rt), Bool.and(LawsBase.wire_fits(rk), ModelFacts.mf.rows_fit(more)), g1)
      +g2 = LLogicBool.wr_and_r(LawsBase.wire_fits(rt), Bool.and(LawsBase.wire_fits(rk), ModelFacts.mf.rows_fit(more)), g1)
      +h3 = LLogicBool.wr_and_l(LawsBase.wire_fits(rk), ModelFacts.mf.rows_fit(more), g2)
      +h4 = LLogicBool.wr_and_r(LawsBase.wire_fits(rk), ModelFacts.mf.rows_fit(more), g2)
      %LAMF.mfb.go(more, rm, rt, rk, tail, h1, h2, h3, h4) : {FMF.run(FMF.get_price(_)) == ModelFacts.mf.mnat(Fx.price(all, m, t), "") : String}
      mfp.tail(all, m, t, hm, ht)

def ModelFacts.model_facts_ffi_price(rows, m, t, fits):
  +hl = LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Fx.PRow, rows)), Bool.and(ModelFacts.mf.rows_fit(rows), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(t))), fits)
  +f1 = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Fx.PRow, rows)), Bool.and(ModelFacts.mf.rows_fit(rows), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(t))), fits)
  +hrows = LLogicBool.wr_and_l(ModelFacts.mf.rows_fit(rows), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(t)), f1)
  +f2 = LLogicBool.wr_and_r(ModelFacts.mf.rows_fit(rows), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(t)), f1)
  +hm = LLogicBool.wr_and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(t), f2)
  +ht = LLogicBool.wr_and_r(LawsBase.wire_fits(m), LawsBase.wire_fits(t), f2)
  mfp.rows(rows, m, t, hl, hrows, hm, ht)

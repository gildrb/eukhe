# eukhe: the proof of LAW model_facts_ffi_effort
# Each of the six entries reads back (LAMF.mfb.ent), then the level.

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

def ModelFacts.model_facts_ffi_effort(m, l, fits):
  match m:
    case Fx.EMap{+mi, +lo, +me, +hi, +xh, +mx}:
      +hmi = LLogicBool.wr_and_l(ModelFacts.mf.ent_fits(mi), Bool.and(ModelFacts.mf.ent_fits(lo), Bool.and(ModelFacts.mf.ent_fits(me), Bool.and(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx))))), fits)
      +rmi = LLogicBool.wr_and_r(ModelFacts.mf.ent_fits(mi), Bool.and(ModelFacts.mf.ent_fits(lo), Bool.and(ModelFacts.mf.ent_fits(me), Bool.and(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx))))), fits)
      +hlo = LLogicBool.wr_and_l(ModelFacts.mf.ent_fits(lo), Bool.and(ModelFacts.mf.ent_fits(me), Bool.and(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx)))), rmi)
      +rlo = LLogicBool.wr_and_r(ModelFacts.mf.ent_fits(lo), Bool.and(ModelFacts.mf.ent_fits(me), Bool.and(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx)))), rmi)
      +hme = LLogicBool.wr_and_l(ModelFacts.mf.ent_fits(me), Bool.and(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx))), rlo)
      +rme = LLogicBool.wr_and_r(ModelFacts.mf.ent_fits(me), Bool.and(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx))), rlo)
      +hhi = LLogicBool.wr_and_l(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx)), rme)
      +rhi = LLogicBool.wr_and_r(ModelFacts.mf.ent_fits(hi), Bool.and(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx)), rme)
      +hxh = LLogicBool.wr_and_l(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx), rhi)
      +rxh = LLogicBool.wr_and_r(ModelFacts.mf.ent_fits(xh), ModelFacts.mf.ent_fits(mx), rhi)
      +hmx = rxh
      %LAMF.mfb.ent(mi, ModelFacts.mf.ent(lo, ModelFacts.mf.ent(me, ModelFacts.mf.ent(hi, ModelFacts.mf.ent(xh, ModelFacts.mf.ent(mx, ModelFacts.mf.elv(l, "")))))), hmi) : {FMF.run(FMF.get_effort(_)) == Wr.put_nat(Fx.effort(Fx.EMap{mi, lo, me, hi, xh, mx}, l), "") : String}
      %LAMF.mfb.ent(lo, ModelFacts.mf.ent(me, ModelFacts.mf.ent(hi, ModelFacts.mf.ent(xh, ModelFacts.mf.ent(mx, ModelFacts.mf.elv(l, ""))))), hlo) : {FMF.run(FMF.get_effort.lo(mi, _)) == Wr.put_nat(Fx.effort(Fx.EMap{mi, lo, me, hi, xh, mx}, l), "") : String}
      %LAMF.mfb.ent(me, ModelFacts.mf.ent(hi, ModelFacts.mf.ent(xh, ModelFacts.mf.ent(mx, ModelFacts.mf.elv(l, "")))), hme) : {FMF.run(FMF.get_effort.me(mi, lo, _)) == Wr.put_nat(Fx.effort(Fx.EMap{mi, lo, me, hi, xh, mx}, l), "") : String}
      %LAMF.mfb.ent(hi, ModelFacts.mf.ent(xh, ModelFacts.mf.ent(mx, ModelFacts.mf.elv(l, ""))), hhi) : {FMF.run(FMF.get_effort.hi(mi, lo, me, _)) == Wr.put_nat(Fx.effort(Fx.EMap{mi, lo, me, hi, xh, mx}, l), "") : String}
      %LAMF.mfb.ent(xh, ModelFacts.mf.ent(mx, ModelFacts.mf.elv(l, "")), hxh) : {FMF.run(FMF.get_effort.xh(mi, lo, me, hi, _)) == Wr.put_nat(Fx.effort(Fx.EMap{mi, lo, me, hi, xh, mx}, l), "") : String}
      %LAMF.mfb.ent(mx, ModelFacts.mf.elv(l, ""), hmx) : {FMF.run(FMF.get_effort.mx(mi, lo, me, hi, xh, _)) == Wr.put_nat(Fx.effort(Fx.EMap{mi, lo, me, hi, xh, mx}, l), "") : String}
      %LAMF.mfb.elv(l, "") : {FMF.run(FMF.get_effort.l(mi, lo, me, hi, xh, mx, _)) == Wr.put_nat(Fx.effort(Fx.EMap{mi, lo, me, hi, xh, mx}, l), "") : String}
      {==}

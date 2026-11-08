# eukhe: the proof of LAW facts_adaptive_else_flag
#
# PROOF: both requests read the answer back (LAMF.mfb.ans); Fx.adaptive
# of None is Fx.flag with the default false, the flag request's decision.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/facts/adaptive.bend as FactsAdaptive
import ../../laws/model_facts.bend as ModelFacts
import ../model_facts/base.bend as LAMF

def ae.main(+a: If.Ans, +fits: {ModelFacts.mf.ans_fits(a) == True{} : Bool}) -> {FMF.ffi(ModelFacts.spell_adaptive(None{}, a)) == FMF.ffi(ModelFacts.spell_flag(a, False{})) : String}:
  %LAMF.mfb.ans(a, "", fits) : {FMF.run(FMF.get_adaptive.a(None{}, _)) == FMF.ffi(ModelFacts.spell_flag(a, False{})) : String}
  %LAMF.mfb.ans(a, Wr.put_bool(False{}, ""), fits) : {FMF.run(FMF.get_adaptive.a(None{}, Wr.Got{a, ""})) == FMF.run(FMF.get_flag(_)) : String}
  {==}

def FactsAdaptive.facts_adaptive_else_flag(a, fits):
  ae.main(a, fits)

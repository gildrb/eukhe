# eukhe: the proof of LAW facts_adaptive_compat_wins
#
# PROOF: the compat flag is a closed prefix and the answer reads back
# (LAMF.mfb.ans); Fx.adaptive of Some{b} is b.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/facts/adaptive.bend as FactsAdaptive
import ../../laws/model_facts.bend as ModelFacts
import ../model_facts/base.bend as LAMF

def aw.main(+b: Bool, +a: If.Ans, +fits: {ModelFacts.mf.ans_fits(a) == True{} : Bool}) -> {FMF.ffi(ModelFacts.spell_adaptive(Some{b}, a)) == Wr.put_bool(b, "") : String}:
  match b:
    case True{}:
      %LAMF.mfb.ans(a, "", fits) : {FMF.run(FMF.get_adaptive.a(Some{True{}}, _)) == Wr.put_bool(True{}, "") : String}
      {==}
    case False{}:
      %LAMF.mfb.ans(a, "", fits) : {FMF.run(FMF.get_adaptive.a(Some{False{}}, _)) == Wr.put_bool(False{}, "") : String}
      {==}

def FactsAdaptive.facts_adaptive_compat_wins(b, a, fits):
  aw.main(b, a, fits)

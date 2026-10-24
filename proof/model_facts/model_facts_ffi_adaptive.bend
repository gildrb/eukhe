# eukhe: the proof of LAW model_facts_ffi_adaptive
# The compat flag is a closed prefix; the answer reads back (LAMF.mfb.ans).

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

def ModelFacts.model_facts_ffi_adaptive(c, a, fits):
  match c:
    case None{}:
      %LAMF.mfb.ans(a, "", fits) : {FMF.run(FMF.get_adaptive.a(None{}, _)) == Wr.put_bool(Fx.adaptive(None{}, a), "") : String}
      {==}
    case Some{b}:
      match b:
        case True{}:
          %LAMF.mfb.ans(a, "", fits) : {FMF.run(FMF.get_adaptive.a(Some{True{}}, _)) == Wr.put_bool(Fx.adaptive(Some{True{}}, a), "") : String}
          {==}
        case False{}:
          %LAMF.mfb.ans(a, "", fits) : {FMF.run(FMF.get_adaptive.a(Some{False{}}, _)) == Wr.put_bool(Fx.adaptive(Some{False{}}, a), "") : String}
          {==}

# eukhe: the proof of LAW model_facts_ffi_flag
# The answer reads back (LAMF.mfb.ans); the default is a closed char.

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

def mff.d(+a: If.Ans, d: Bool, +h: {ModelFacts.mf.ans_fits(a) == True{} : Bool}) -> {FMF.ffi(ModelFacts.spell_flag(a, d)) == Wr.put_bool(Fx.flag(a, d), "") : String}:
  match d:
    case True{}:
      %LAMF.mfb.ans(a, Wr.put_bool(True{}, ""), h) : {FMF.run(FMF.get_flag(_)) == Wr.put_bool(Fx.flag(a, True{}), "") : String}
      {==}
    case False{}:
      %LAMF.mfb.ans(a, Wr.put_bool(False{}, ""), h) : {FMF.run(FMF.get_flag(_)) == Wr.put_bool(Fx.flag(a, False{}), "") : String}
      {==}

def ModelFacts.model_facts_ffi_flag(a, d, fits):
  mff.d(a, d, fits)

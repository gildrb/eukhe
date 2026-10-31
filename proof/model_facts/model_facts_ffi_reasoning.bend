# eukhe: the proof of LAW model_facts_ffi_reasoning
# The shape, the entry and the level read back (LAMF.mfb.*); the entry's
# reply is the laws' reply form (LAMF.mfb.rfields).

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/wire.bend as Wr
import ../../laws/model_facts.bend as ModelFacts
import ./base.bend as LAMF

def ModelFacts.model_facts_ffi_reasoning(s, e, l, fits):
  %LAMF.mfb.shape(s, ModelFacts.mf.ent(e, ModelFacts.mf.elv(l, ""))) : {FMF.run(FMF.get_reasoning(_)) == ModelFacts.mf.rfields(Fx.reasoning(s, e, l)) : String}
  %LAMF.mfb.ent(e, ModelFacts.mf.elv(l, ""), fits) : {FMF.run(FMF.get_reasoning.e(s, _)) == ModelFacts.mf.rfields(Fx.reasoning(s, e, l)) : String}
  %LAMF.mfb.elv(l, "") : {FMF.run(FMF.get_reasoning.l(s, e, _)) == ModelFacts.mf.rfields(Fx.reasoning(s, e, l)) : String}
  LAMF.mfb.rfields(Fx.reasoning(s, e, l))

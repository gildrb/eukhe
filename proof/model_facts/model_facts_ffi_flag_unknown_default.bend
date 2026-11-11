# eukhe: the proof of LAW model_facts_ffi_flag_unknown_default
# Each default is a closed request; the entry runs on it.

import Base
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/model_facts.bend as ModelFacts

def mfu.d(d: Bool) -> {FMF.ffi(ModelFacts.spell_flag(If.Unknown{}, d)) == Wr.put_bool(d, "") : String}:
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

def ModelFacts.model_facts_ffi_flag_unknown_default(d):
  mfu.d(d)

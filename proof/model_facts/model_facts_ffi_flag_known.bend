# eukhe: the proof of LAW model_facts_ffi_flag_known
# The answer reads back (LAMF.mfb.ans); the default is a closed char.

import Base
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/model_facts.bend as ModelFacts
import ./base.bend as LAMF

def mfk.d(+v: Nat, d: Bool, +h: {LawsBase.wire_fits(v) == True{} : Bool}) -> {FMF.ffi(ModelFacts.spell_flag(If.Known{v}, d)) == Wr.put_bool(Nat.is_eq(v, 1n), "") : String}:
  match d:
    case True{}:
      %LAMF.mfb.ans(If.Known{v}, Wr.put_bool(True{}, ""), h) : {FMF.run(FMF.get_flag(_)) == Wr.put_bool(Nat.is_eq(v, 1n), "") : String}
      {==}
    case False{}:
      %LAMF.mfb.ans(If.Known{v}, Wr.put_bool(False{}, ""), h) : {FMF.run(FMF.get_flag(_)) == Wr.put_bool(Nat.is_eq(v, 1n), "") : String}
      {==}

def ModelFacts.model_facts_ffi_flag_known(v, d, fits):
  mfk.d(v, d, fits)

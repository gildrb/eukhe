# eukhe: lemmas of the entry proofs of area codemode_source: the replies
#
# The entry's encoder is the spec's speller (laws/codemode_source.bend
# spell_answer), so its answer is the spelled answer of the model
# (csy.answer), and no answer opens with 'E' (csy.not_err).

import Base
import ../../../bend/codemode_source.bend as Src
import ../../../bend/ffi_codemode_source.bend as FSrc
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/codemode_source.bend as CodemodeSource

# the entry's encoder spells an answer as the spec does
def csy.answer(a: Src.Answer) -> {FSrc.put_answer(a) == CodemodeSource.spell_answer(a) : String}:
  match a:
    case Src.Refuse{t}:
      {==}
    case Src.Plain{}:
      {==}
    case Src.Split{k, o}:
      {==}

# no answer of the entry opens with 'E'
def csy.not_err(a: Src.Answer) -> {LawsBase.wire_opens_err(FSrc.put_answer(a)) == False{} : Bool}:
  match a:
    case Src.Refuse{t}:
      Wire.wire_nat_not_err(0n, Wr.put_str(t, ""))
    case Src.Plain{}:
      Wire.wire_nat_not_err(1n, "")
    case Src.Split{k, o}:
      Wire.wire_nat_not_err(2n, Wr.put_bool(k, Wr.put_bool(o, "")))

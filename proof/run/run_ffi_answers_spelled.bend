# eukhe: the proof of LAW run_ffi_answers_spelled
#
# PROOF: the spelled request is the entry's encoding of it (LSp.sp.ask), so
# the entry answers it with its answer (run_ffi_answers), the spelled value
# of its decision (LSp.sp.answer).

import Base
import ../../bend/ffi_run.bend as FRn
import ../../laws/run/entry.bend as Run
import ./run_ffi_answers.bend as PRunFfiAnswers
import ./run_ffi_answers_spelled/spell.bend as LSp

def Run.run_ffi_answers_spelled(a, fits):
  %LSp.sp.ask(a, "") : {FRn.ffi(_) == Run.run_spell_answer(a) : String}
  %LSp.sp.answer(a) : {FRn.ffi(FRn.put_ask(a, "")) == _ : String}
  Run.run_ffi_answers(a, fits)

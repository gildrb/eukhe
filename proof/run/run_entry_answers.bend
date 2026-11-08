# eukhe: the proof of LAW run_entry_answers
#
# PROOF: run_entry_exact on the spelled request, which the reader reads
# back whole with nothing left (run_entry_reads).

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/wire.bend as Wr
import ./run_entry_reads.bend as PRunEntryReads
import ../../laws/run/spec.bend as RunSpec
import ./base/entry.bend as LARunEntry

def RunSpec.run_entry_answers(a, h):
  +q = RunSpec.re.w_ask(a, "")
  %Equal.sym(String, FRn.ffi(q), RunSpec.re.entry(q), LARunEntry.rex.exact(q)) : {_ == RunSpec.re.answer(a) : String}
  %Equal.sym(Wr.Dec<FRn.Ask>, RunSpec.re.r_ask(q), Wr.Got{a, ""}, RunSpec.run_entry_reads(a, "", h)) : {RunSpec.re.entry.go(_) == RunSpec.re.answer(a) : String}
  {==}

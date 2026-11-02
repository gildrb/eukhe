# eukhe: the proof of LAW run_entry_answers
#
# PROOF: run_entry_exact on the spelled request, which the reader reads
# back whole with nothing left (run_entry_reads).

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/wire.bend as Wr
import ./run_entry_reads.bend as PRunEntryReads
import ../../laws/run/entry.bend as RunEntry
import ./base/entry.bend as LARunEntry

def RunEntry.run_entry_answers(a, h):
  +q = RunEntry.re.w_ask(a, "")
  %Equal.sym(String, FRn.ffi(q), RunEntry.re.entry(q), LARunEntry.rex.exact(q)) : {_ == RunEntry.re.answer(a) : String}
  %Equal.sym(Wr.Dec<FRn.Ask>, RunEntry.re.r_ask(q), Wr.Got{a, ""}, RunEntry.run_entry_reads(a, "", h)) : {RunEntry.re.entry.go(_) == RunEntry.re.answer(a) : String}
  {==}

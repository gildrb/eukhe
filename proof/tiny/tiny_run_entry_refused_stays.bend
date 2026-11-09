# eukhe: the proof of LAW tiny_run_entry_refused_stays
#
# PROOF: a refused open opens the refused state with the malformed-open
# error (tiny_run_entry_open_refuses); from the refused state every step,
# whatever its input, keeps it and answers the refused error, so by
# induction on the inputs each later answer is that error.

import Base
import ../../bend/ffi_tiny_run.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/tiny/run.bend as TinyRun
import ./tiny_run_entry_open_refuses.bend as PTinyRunEntryOpenRefuses

# from the refused state answering o, the answers to ins
def trr.go(ins: List<&2, String>, +o: String) -> {TinyRun.tr_raw(ins, (FTr.Refused{}, o)) == o <> TinyRun.tr_each(ins, Wr.err("tiny_run: the open was refused")) : List<&2, String>}:
  match ins:
    case Nil{}:
      {==}
    case i <> t:
      Equal.cong(List<&2, String>, List<&2, String>, z => o <> z, TinyRun.tr_raw(t, (FTr.Refused{}, Wr.err("tiny_run: the open was refused"))), Wr.err("tiny_run: the open was refused") <> TinyRun.tr_each(t, Wr.err("tiny_run: the open was refused")), trr.go(t, Wr.err("tiny_run: the open was refused")))

def TinyRun.tiny_run_entry_refused_stays(s, bad, ins):
  %Equal.sym(FTr.St & String, FTr.open(s), (FTr.Refused{}, Wr.err("tiny_run: malformed open")), TinyRun.tiny_run_entry_open_refuses(s, bad)) : {TinyRun.tr_raw(ins, _) == Wr.err("tiny_run: malformed open") <> TinyRun.tr_each(ins, Wr.err("tiny_run: the open was refused")) : List<&2, String>}
  trr.go(ins, Wr.err("tiny_run: malformed open"))

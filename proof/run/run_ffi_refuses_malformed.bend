# eukhe: the proof of LAW run_ffi_refuses_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_run.bend as FRn
import ../../LAWS.bend as Laws

def Laws.run_ffi_refuses_malformed(s, bad):
  %Equal.sym(Wr.Dec<FRn.Ask>, FRn.get_ask(s), Wr.Bad{}, bad) : {FRn.ffi.go(_) == Wr.err("run: malformed request") : String}
  {==}

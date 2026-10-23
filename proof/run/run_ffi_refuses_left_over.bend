# eukhe: the proof of LAW run_ffi_refuses_left_over

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/wire.bend as Wr
import ../../laws/run.bend as Run
import ./base.bend as LA

def Run.run_ffi_refuses_left_over(a, rest, h, more):
  %Equal.sym(Wr.Dec<FRn.Ask>, FRn.get_ask(FRn.put_ask(a, rest)), Wr.Got{a, rest}, LA.rk.rt_ask(a, rest, h)) : {FRn.ffi.go(_) == Wr.err("run: input left over after the request") : String}
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FRn.ffi.end(_, a) == Wr.err("run: input left over after the request") : String}
  {==}

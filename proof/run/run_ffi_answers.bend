# eukhe: the proof of LAW run_ffi_answers

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/wire.bend as Wr
import ../../laws/run.bend as Run
import ./base.bend as LA

def Run.run_ffi_answers(a, h):
  %Equal.sym(Wr.Dec<FRn.Ask>, FRn.get_ask(FRn.put_ask(a, "")), Wr.Got{a, ""}, LA.rk.rt_ask(a, "", h)) : {FRn.ffi.go(_) == FRn.answer(a) : String}
  {==}

# eukhe: the proof of LAW run_ffi_answers

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_run.bend as FRn
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.run_ffi_answers(a, h):
  %Equal.sym(Wr.Dec<FRn.Ask>, FRn.get_ask(FRn.put_ask(a, "")), Wr.Got{a, ""}, LA.rk.rt_ask(a, "", h)) : {FRn.ffi.go(_) == FRn.answer(a) : String}
  {==}

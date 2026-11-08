# eukhe: the proof of LAW log_stepper_left_over
#
# The sidecar entries read back with the rest untouched (pe.rt); the end
# check sees the char left and answers the left-over error.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/log.bend as Log
import ./base.bend as LA

def Log.log_stepper_left_over(st, ds, fits, c, t):
  %Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_list(~Bool, ~Wr.put_bool, ds, SCon{c, t})), Wr.Got{ds, SCon{c, t}}, LA.pe.rt(ds, SCon{c, t}, fits)) : {Log.log_reply(FLg.step.go(st, _)) == Wr.err("log: input left over") : String}
  {==}

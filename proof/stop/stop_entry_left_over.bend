# eukhe: the proof of LAW stop_entry_left_over
#
# PROOF: the spelled request reads back with the rest after it (LA.stb.req); the rest is not empty, so the entry answers the error.

import Base
import ../../bend/ffi_stop.bend as FS
import ../../bend/wire.bend as Wr
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_entry_left_over(a, rest, h, more):
  %Equal.sym(Wr.Dec<FS.Ask>, FS.get_ask(Stop.sp_w_ask(a, rest)), Wr.Got{a, rest}, LA.stb.req(a, rest, h)) : {FS.ffi.got(_) == Wr.err("stop: malformed request") : String}
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FS.ffi.done(a, _) == Wr.err("stop: malformed request") : String}
  {==}

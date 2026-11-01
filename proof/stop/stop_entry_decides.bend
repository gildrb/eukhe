# eukhe: the proof of LAW stop_entry_decides
#
# PROOF: the spelled request reads back whole, nothing left (LA.stb.req); the answer is the spelled spec answer (LA.stb.reply).

import Base
import ../../bend/ffi_stop.bend as FS
import ../../bend/wire.bend as Wr
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_entry_decides(a, h):
  %Equal.sym(Wr.Dec<FS.Ask>, FS.get_ask(Stop.sp_w_ask(a, "")), Wr.Got{a, ""}, LA.stb.req(a, "", h)) : {FS.ffi.got(_) == Stop.sp_w_reply(a) : String}
  LA.stb.reply(a)

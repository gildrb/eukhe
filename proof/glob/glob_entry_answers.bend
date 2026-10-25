# eukhe: the proof of LAW glob_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (ge.req), so the entry answers the model's decision, which is the spec's (glob_groups, glob_allowed; a check spells parse's error).

import Base
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/entry.bend as GE

def Glob.glob_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FG.Req>, FG.get_req(Glob.sp_w_req(q, "")), Wr.Got{q, ""}, GE.ge.req(q, "", h)) : {FG.ffi.got(_) == Glob.sp_w_reply(q) : String}
  GE.ge.reply(q)

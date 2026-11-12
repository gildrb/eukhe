# eukhe: the proof of LAW dash_access_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (dash_access_entry_reads), so the entry answers the model's verdict,
# spelled (daa.reply: case by case).

import Base
import ../../bend/dash_access.bend as Ac
import ../../bend/ffi_dash_access.bend as FAc
import ../../bend/wire.bend as Wr
import ../../laws/dash_access.bend as DashAccess
import ./dash_access_entry_reads.bend as PDashAccessEntryReads

def daa.reply(q: FAc.Req) -> {FAc.answer(q) == DashAccess.sp_w_reply(q) : String}:
  match q:
    case FAc.QHost{hh, al}:
      {==}
    case FAc.QOrigin{o, hh}:
      {==}

def DashAccess.dash_access_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FAc.Req>, FAc.get_req(DashAccess.sp_w_req(q, "")), Wr.Got{q, ""}, DashAccess.dash_access_entry_reads(q, "", h)) : {FAc.ffi.got(_) == DashAccess.sp_w_reply(q) : String}
  daa.reply(q)

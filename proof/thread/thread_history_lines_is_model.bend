# eukhe: the proof of LAW thread_history_lines_is_model
#
# PROOF: the spelled request reads back whole with nothing left
# (thread_entry_reads), so the entry answers the model's count, spelled
# (thm.reply).

import Base
import ../../bend/thread.bend as Th
import ../../bend/ffi_thread.bend as FTh
import ../../bend/wire.bend as Wr
import ../../laws/thread.bend as Thread
import ./thread_entry_reads.bend as PThreadEntryReads

def thm.reply(q: FTh.Req) -> {FTh.answer(q) == Thread.sp_w_reply(q) : String}:
  match q:
    case FTh.Req{t, v, xs}:
      {==}

def Thread.thread_history_lines_is_model(q, h):
  %Equal.sym(Wr.Dec<FTh.Req>, FTh.get_req(Thread.sp_w_req(q, "")), Wr.Got{q, ""}, Thread.thread_entry_reads(q, "", h)) : {FTh.ffi.got(_) == Thread.sp_w_reply(q) : String}
  thm.reply(q)

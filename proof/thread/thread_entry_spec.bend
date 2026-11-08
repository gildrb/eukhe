# eukhe: the proof of LAW thread_entry_spec
#
# PROOF: the entry answers the model's count, spelled
# (thread_history_lines_is_model); that count is the spec's
# (thread_history_lines_spec), so the spelling is the spec's (thes.reply).

import Base
import ../../bend/thread.bend as Th
import ../../bend/ffi_thread.bend as FTh
import ../../bend/wire.bend as Wr
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./thread_history_lines_is_model.bend as PThreadHistoryLinesIsModel
import ./thread_history_lines_spec.bend as PThreadHistoryLinesSpec

# the model's reply is the spec's
def thes.reply(q: FTh.Req) -> {Thread.sp_w_reply(q) == Thread.sp_w_spec_reply(q) : String}:
  match q:
    case FTh.Req{+t, +v, +xs}:
      %Thread.thread_history_lines_spec(t, v, xs) : {Wr.put_nat(Th.history_lines(t, v, xs), "") == Wr.put_nat(_, "") : String}
      {==}

def Thread.thread_entry_spec(q, h):
  Equal.trans(String, FTh.ffi(Thread.sp_w_req(q, "")), Thread.sp_w_reply(q), Thread.sp_w_spec_reply(q), Thread.thread_history_lines_is_model(q, h), thes.reply(q))

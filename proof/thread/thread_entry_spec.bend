# eukhe: the proof of LAW thread_entry_spec
#
# PROOF: the count is the model's (witness Th.history_lines): the entry
# answers it, spelled (thread_history_lines_is_model), and it is the
# length of the leading run of starts below end
# (thread_history_lines_run).

import Base
import ../../bend/thread.bend as Th
import ../../bend/ffi_thread.bend as FTh
import ../../laws/thread.bend as Thread
import ./thread_history_lines_is_model.bend as PThreadHistoryLinesIsModel
import ./thread_history_lines_run.bend as PThreadHistoryLinesRun

def Thread.thread_entry_spec(q, h):
  match q:
    case FTh.Req{+t, +v, +xs}:
      (Th.history_lines(t, v, xs), (Thread.thread_history_lines_is_model(FTh.Req{t, v, xs}, h), Thread.thread_history_lines_run(t, v, xs)))

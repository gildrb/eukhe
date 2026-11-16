# eukhe: the proof of LAW work_list_entry_is_model
#
# PROOF: the spelled request reads back whole with nothing left
# (work_list_entry_reads), so the entry answers the model's hand-back,
# encoded as the spec spells it (wlm.reply).

import Base
import ../../bend/work_list.bend as Wl
import ../../bend/ffi_work_list.bend as FWl
import ../../bend/wire.bend as Wr
import ../../laws/work_list.bend as WorkList
import ./work_list_entry_reads.bend as PWorkListEntryReads

def wlm.reply(o: Wl.Outcome) -> {FWl.put_outcome(o) == WorkList.sp_w_reply(o) : String}:
  match o:
    case Wl.Finished{}:
      {==}
    case Wl.Stopped{xs}:
      {==}

def WorkList.work_list_entry_is_model(done, h):
  %Equal.sym(Wr.Dec<List<&2, Bool>>, FWl.get_req(WorkList.sp_w_req(done, "")), Wr.Got{done, ""}, WorkList.work_list_entry_reads(done, "", h)) : {FWl.ffi.got(_) == WorkList.sp_w_reply(Wl.outcome(done)) : String}
  wlm.reply(Wl.outcome(done))

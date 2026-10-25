# eukhe: the proof of LAW work_entry_open_refused

import Base
import ../../laws/work.bend as Work
import ../../bend/ffi_work.bend as FW
import ../../bend/wire.bend as Wr

def Work.work_entry_open_refused(s, h):
  %Equal.sym(Bool, String.is_empty(s), False{}, h) : {FW.open.go(_) == (FW.Shut{}, Wr.err("work: the open takes no input")) : FW.St & String}
  {==}

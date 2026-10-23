# eukhe: the proof of LAW restart_ffi_malformed

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/supervise.bend as Supervise

def Supervise.restart_ffi_malformed(s, h):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(s), Wr.Bad{}, h) : {FS.ffi.go(_) == Wr.err("supervise: malformed request") : String}
  {==}

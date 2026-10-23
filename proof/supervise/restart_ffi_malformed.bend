# eukhe: the proof of LAW restart_ffi_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_supervise.bend as FS
import ../../LAWS.bend as Laws

def Laws.restart_ffi_malformed(s, h):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(s), Wr.Bad{}, h) : {FS.ffi.go(_) == Wr.err("supervise: malformed request") : String}
  {==}

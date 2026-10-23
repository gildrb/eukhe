# eukhe: the proof of LAW dir_ffi_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_director.bend as FDr
import ../../LAWS.bend as Laws

def Laws.dir_ffi_malformed(s, h):
  Equal.cong(Wr.Dec<FDr.Req>, String, d => FDr.ffi.go(d), FDr.get_req(s), Wr.Bad{}, h)

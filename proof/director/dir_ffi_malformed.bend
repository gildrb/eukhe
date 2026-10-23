# eukhe: the proof of LAW dir_ffi_malformed

import Base
import ../../bend/ffi_director.bend as FDr
import ../../bend/wire.bend as Wr
import ../../laws/director.bend as Director

def Director.dir_ffi_malformed(s, h):
  Equal.cong(Wr.Dec<FDr.Req>, String, d => FDr.ffi.go(d), FDr.get_req(s), Wr.Bad{}, h)

# eukhe: the proof of LAW dir_ffi_is_tick

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_director.bend as FDr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.dir_ffi_is_tick(c, l, vs, h):
  Equal.cong(Wr.Dec<FDr.Req>, String, d => FDr.ffi.go(d), FDr.get_req(FDr.put_req(FDr.Req{c, l, vs}, "")), Wr.Got{FDr.Req{c, l, vs}, ""}, LA.pdf.req_rt(FDr.Req{c, l, vs}, "", h))

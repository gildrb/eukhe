# eukhe: the proof of LAW dir_ffi_is_tick

import Base
import ../../bend/ffi_director.bend as FDr
import ../../bend/wire.bend as Wr
import ../../laws/director.bend as Director
import ./base.bend as LA

def Director.dir_ffi_is_tick(c, l, vs, h):
  Equal.cong(Wr.Dec<FDr.Req>, String, d => FDr.ffi.go(d), FDr.get_req(FDr.put_req(FDr.Req{c, l, vs}, "")), Wr.Got{FDr.Req{c, l, vs}, ""}, LA.pdf.req_rt(FDr.Req{c, l, vs}, "", h))

# eukhe: the proof of LAW dir_ffi_left_over

import Base
import ../../bend/ffi_director.bend as FDr
import ../../bend/wire.bend as Wr
import ../../laws/director.bend as Director

def Director.dir_ffi_left_over(s, q, r, h, e):
  Equal.trans(String, FDr.ffi.go(FDr.get_req(s)), FDr.ffi.go(Wr.Got{q, r}), Wr.err("director: input left over"), Equal.cong(Wr.Dec<FDr.Req>, String, d => FDr.ffi.go(d), FDr.get_req(s), Wr.Got{q, r}, h), Equal.cong(Bool, String, b => FDr.ffi.whole(q, b), String.is_empty(r), False{}, e))

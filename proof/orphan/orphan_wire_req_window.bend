# eukhe: the proof of LAW orphan_wire_req_window

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/orphan.bend as Orphan
import ../base.bend as L
import ./base.bend as LA

def Orphan.orphan_wire_req_window(w, hw, a, ha, k, rest):
  +r = rest
  %L.ps.ffi_nat(w, Wr.put_nat(a, FO.put_work(k, r)), hw) : {FO.get_req.window(FO.get_window.some(_)) == Wr.Got{FO.Req{Some{w}, a, k}, r} : Wr.Dec<FO.Req>}
  %L.ps.ffi_nat(a, FO.put_work(k, r), ha) : {FO.get_req.absent(Some{w}, _) == Wr.Got{FO.Req{Some{w}, a, k}, r} : Wr.Dec<FO.Req>}
  %LA.ps.ffi_work(k, r) : {FO.get_req.work(Some{w}, a, _) == Wr.Got{FO.Req{Some{w}, a, k}, r} : Wr.Dec<FO.Req>}
  {==}

# eukhe: the proof of LAW orphan_wire_req_no_window

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_orphan.bend as FO
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def Laws.orphan_wire_req_no_window(a, ha, k, rest):
  +r = rest
  %L.ps.ffi_nat(a, FO.put_work(k, r), ha) : {FO.get_req.absent(None{}, _) == Wr.Got{FO.Req{None{}, a, k}, r} : Wr.Dec<FO.Req>}
  %LA.ps.ffi_work(k, r) : {FO.get_req.work(None{}, a, _) == Wr.Got{FO.Req{None{}, a, k}, r} : Wr.Dec<FO.Req>}
  {==}

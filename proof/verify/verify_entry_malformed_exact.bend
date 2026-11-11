# eukhe: the proof of LAW verify_entry_malformed_exact
#
# PROOF: the entry reads every input as the laws' reader does (vr.req);
# where that reader finds no whole request, the entry answers its error
# form (vr.got_none: a request read whole contradicts the premise).

import Base
import ../../bend/verify.bend as V
import ../../bend/ffi_verify.bend as FV
import ../../bend/wire.bend as Wr
import ../../spec/verified/verify_wire.bend as SW
import ../../laws/verify.bend as Verify
import ./base/read.bend as LR

def Verify.verify_entry_malformed_exact(s, no):
  %Equal.sym(Wr.Dec<FV.Req>, FV.get_req(Wr.get_nat(s)), SW.r_req(Wr.get_nat(s)), LR.vr.req(Wr.get_nat(s))) : {FV.ffi.got(_) == Wr.err("verify: malformed request") : String}
  LR.vr.got_none(SW.r_req(Wr.get_nat(s)), no)

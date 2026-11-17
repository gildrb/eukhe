# eukhe: the proof of LAW strength_entry_malformed_exact
#
# PROOF: the entry reads every input as the laws' reader does (LR.sr.req);
# where that reader finds no whole request, the entry answers its error
# form (LR.sr.got_none: a request read whole contradicts the premise).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/ffi_strength.bend as FS
import ../../bend/wire.bend as Wr
import ../../spec/verified/strength_wire.bend as SW
import ../../laws/strength.bend as Strength
import ./base/read.bend as LR

def Strength.strength_entry_malformed_exact(s, no):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(Wr.get_nat(s)), SW.r_req(Wr.get_nat(s)), LR.sr.req(Wr.get_nat(s))) : {FS.ffi.got(_) == Wr.err("strength: malformed request") : String}
  LR.sr.got_none(SW.r_req(Wr.get_nat(s)), no)

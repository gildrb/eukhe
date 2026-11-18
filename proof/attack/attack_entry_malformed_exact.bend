# eukhe: the proof of LAW attack_entry_malformed_exact
#
# PROOF: the entry reads every input as the laws' reader does (LR.ar.req);
# where that reader finds no whole request, the entry answers its error
# form (LR.ar.got_none).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/attack.bend as At
import ../../bend/ffi_attack.bend as FA
import ../../bend/wire.bend as Wr
import ../../spec/verified/attack_wire.bend as SAW
import ../../laws/attack.bend as Attack
import ./base/read.bend as LR

def Attack.attack_entry_malformed_exact(s, no):
  %Equal.sym(Wr.Dec<FA.Req>, FA.get_req(Wr.get_nat(s)), SAW.r_req(Wr.get_nat(s)), LR.ar.req(Wr.get_nat(s))) : {FA.ffi.got(_) == Wr.err("attack: malformed request") : String}
  LR.ar.got_none(SAW.r_req(Wr.get_nat(s)), no)

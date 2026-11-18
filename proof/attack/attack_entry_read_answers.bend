# eukhe: the proof of LAW attack_entry_read_answers
#
# PROOF: the entry reads every input as the laws' reader does (LR.ar.req);
# where that reader finds the whole request q, the entry answers its
# decision on q (LR.ar.got_some), encoded as the spec spells it
# (LE.ae.answer).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/attack.bend as At
import ../../bend/ffi_attack.bend as FA
import ../../bend/wire.bend as Wr
import ../../spec/verified/attack_wire.bend as SAW
import ../../laws/attack.bend as Attack
import ./base/entry.bend as LE
import ./base/read.bend as LR

def Attack.attack_entry_read_answers(s, q, got):
  %Equal.sym(Wr.Dec<FA.Req>, FA.get_req(Wr.get_nat(s)), SAW.r_req(Wr.get_nat(s)), LR.ar.req(Wr.get_nat(s))) : {FA.ffi.got(_) == SAW.w_reply(q) : String}
  %LE.ae.answer(q) : {FA.ffi.got(SAW.r_req(Wr.get_nat(s))) == _ : String}
  LR.ar.got_some(SAW.r_req(Wr.get_nat(s)), q, got)

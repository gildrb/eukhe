# eukhe: the proof of LAW strength_entry_read_answers
#
# PROOF: the entry reads every input as the laws' reader does (LR.sr.req);
# where that reader finds the whole request q, the entry answers its
# decision on q (LR.sr.got_some), encoded as the spec spells it
# (LE.se.answer).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/ffi_strength.bend as FS
import ../../bend/wire.bend as Wr
import ../../spec/verified/strength_wire.bend as SW
import ../../laws/strength.bend as Strength
import ./base/entry.bend as LE
import ./base/read.bend as LR

def Strength.strength_entry_read_answers(s, q, got):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(Wr.get_nat(s)), SW.r_req(Wr.get_nat(s)), LR.sr.req(Wr.get_nat(s))) : {FS.ffi.got(_) == SW.w_reply(q) : String}
  %LE.se.answer(q) : {FS.ffi.got(SW.r_req(Wr.get_nat(s))) == _ : String}
  LR.sr.got_some(SW.r_req(Wr.get_nat(s)), q, got)

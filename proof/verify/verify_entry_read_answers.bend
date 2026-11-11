# eukhe: the proof of LAW verify_entry_read_answers
#
# PROOF: the entry reads every input as the laws' reader does (vr.req);
# where that reader finds the whole request q, the entry answers its
# decision on q (vr.got_some), encoded as the spec spells it (ve.answer).

import Base
import ../../bend/verify.bend as V
import ../../bend/ffi_verify.bend as FV
import ../../bend/wire.bend as Wr
import ../../spec/verified/verify_wire.bend as SW
import ../../laws/verify.bend as Verify
import ./base/entry.bend as LE
import ./base/read.bend as LR

def Verify.verify_entry_read_answers(s, q, got):
  %Equal.sym(Wr.Dec<FV.Req>, FV.get_req(Wr.get_nat(s)), SW.r_req(Wr.get_nat(s)), LR.vr.req(Wr.get_nat(s))) : {FV.ffi.got(_) == SW.w_reply(q) : String}
  %LE.ve.answer(q) : {FV.ffi.got(SW.r_req(Wr.get_nat(s))) == _ : String}
  LR.vr.got_some(SW.r_req(Wr.get_nat(s)), q, got)

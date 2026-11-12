# eukhe: the proof of LAW verify_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (ve.req),
# so the entry answers the model's decision, encoded as the spec spells it
# (ve.answer).

import Base
import ../../bend/verify.bend as V
import ../../bend/ffi_verify.bend as FV
import ../../bend/wire.bend as Wr
import ../../spec/verified/verify_wire.bend as SW
import ../../laws/verify.bend as Verify
import ./base/entry.bend as LE

def Verify.verify_entry_answers(q, fit):
  %LE.ve.req(q, "", fit) : {FV.ffi.got(_) == SW.w_reply(q) : String}
  LE.ve.answer(q)

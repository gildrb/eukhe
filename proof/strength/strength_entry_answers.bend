# eukhe: the proof of LAW strength_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (LE.se.req), so
# the entry answers the model's decision, encoded as the spec spells it
# (LE.se.answer).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/ffi_strength.bend as FS
import ../../bend/wire.bend as Wr
import ../../spec/verified/strength_wire.bend as SW
import ../../laws/strength.bend as Strength
import ./base/entry.bend as LE

def Strength.strength_entry_answers(q, fit):
  %LE.se.req(q, "", fit) : {FS.ffi.got(_) == SW.w_reply(q) : String}
  LE.se.answer(q)

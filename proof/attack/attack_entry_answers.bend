# eukhe: the proof of LAW attack_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (LE.ae.req), so
# the entry answers the model's decision, encoded as the spec spells it
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

def Attack.attack_entry_answers(q, fit):
  %LE.ae.req(q, "", fit) : {FA.ffi.got(_) == SAW.w_reply(q) : String}
  LE.ae.answer(q)

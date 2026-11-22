# eukhe: the proof of LAW attack_entry_leftover_refused
#
# PROOF: the entry's decoder reads the spelled request back with the input
# after it untouched (LE.ae.req); that input is not empty, so the entry
# answers its error form.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/attack.bend as At
import ../../bend/ffi_attack.bend as FA
import ../../bend/wire.bend as Wr
import ../../spec/verified/attack_wire.bend as SAW
import ../../laws/attack.bend as Attack
import ./base/entry.bend as LE

def Attack.attack_entry_leftover_refused(q, c, r, fit):
  %LE.ae.req(q, SCon{c, r}, fit) : {FA.ffi.got(_) == Wr.err("attack: malformed request") : String}
  {==}

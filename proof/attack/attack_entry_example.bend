# eukhe: the proof of LAW attack_entry_example
#
# PROOF: closed: both sides compute.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/attack.bend as At
import ../../bend/ffi_attack.bend as FA
import ../../bend/wire.bend as Wr
import ../../spec/verified/attack_wire.bend as SAW
import ../../laws/attack.bend as Attack

def Attack.attack_entry_example():
  {==}

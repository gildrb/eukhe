# eukhe: the proof of LAW strength_entry_leftover_refused
#
# PROOF: the entry's decoder reads the spelled request back with the input
# after it untouched (LE.se.req); that input is not empty, so the entry
# answers its error form.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/ffi_strength.bend as FS
import ../../bend/wire.bend as Wr
import ../../spec/verified/strength_wire.bend as SW
import ../../laws/strength.bend as Strength
import ./base/entry.bend as LE

def Strength.strength_entry_leftover_refused(q, c, r, fit):
  %LE.se.req(q, SCon{c, r}, fit) : {FS.ffi.got(_) == Wr.err("strength: malformed request") : String}
  {==}

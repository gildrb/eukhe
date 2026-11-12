# eukhe: the proof of LAW verify_entry_leftover_refused
#
# PROOF: the entry's decoder reads the spelled request back with the input
# after it untouched (LE.ve.req); that input is not empty, so the entry
# answers its error form.

import Base
import ../../bend/verify.bend as V
import ../../bend/ffi_verify.bend as FV
import ../../bend/wire.bend as Wr
import ../../spec/verified/verify_wire.bend as SW
import ../../laws/verify.bend as Verify
import ./base/entry.bend as LE

def Verify.verify_entry_leftover_refused(q, c, r, fit):
  %LE.ve.req(q, SCon{c, r}, fit) : {FV.ffi.got(_) == Wr.err("verify: malformed request") : String}
  {==}

# eukhe: the proof of LAW replace_ffi_verdict_spelled
#
# PROOF of LAW replace_ffi_verdict_spelled: the spelled request reads
# back whole, caller included (rfe.read), so the entry answers it
# (rfe.ffi), and its answer is the spelled verdict_spec (rfe.answer).

import Base
import ../../bend/ffi_replace.bend as FRp
import ../../laws/replace.bend as Replace
import ./base.bend as LAReplace

def Replace.replace_ffi_verdict_spelled(c, d, same, k, f):
  LAReplace.rfe.ffi(FRp.ReqVerdict{c, d, same, k}, f)

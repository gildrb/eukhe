# eukhe: the proof of LAW replace_ffi_relation_spelled
#
# PROOF of LAW replace_ffi_relation_spelled: the spelled request reads
# back whole (rfe.read), so the entry answers it (rfe.ffi), and its answer
# is the spelled Rel tag of rp_rel_of (rfe.answer).

import Base
import ../../bend/ffi_replace.bend as FRp
import ../../laws/replace.bend as Replace
import ./base.bend as LAReplace

def Replace.replace_ffi_relation_spelled(c, d, same, f):
  LAReplace.rfe.ffi(FRp.ReqRelation{c, d, same}, f)

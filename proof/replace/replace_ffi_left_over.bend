# eukhe: the proof of LAW replace_ffi_left_over
#
# PROOF of LAW replace_ffi_left_over: the spelled request reads back with
# the rest after it untouched (rfe.read); that rest is not empty, so the
# entry answers the left-over error.

import Base
import ../../bend/ffi_replace.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/replace.bend as Replace
import ./base.bend as LAReplace

def Replace.replace_ffi_left_over(q, f, ch, t):
  %Equal.sym(Wr.Dec<FRp.Req>, FRp.get_req(Replace.rp_spell_req(q, SCon{ch, t})), Wr.Got{q, SCon{ch, t}}, LAReplace.rfe.read(q, SCon{ch, t}, f)) : {FRp.ffi.of(_) == Wr.err("replace: input left over") : String}
  {==}

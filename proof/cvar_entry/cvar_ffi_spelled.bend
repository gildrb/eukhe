# eukhe: the proof of LAW cvar_ffi_spelled
# The spec's spelling is the entry's encoding (LB.cve.put_xreq), which the
# entry answers with the model's expansion (cvar_ffi_is_expand), the
# spec's (alias_expand_exact), spelled as the spec spells it.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as Cvar
import ../../laws/cvar_entry.bend as CvarEntry
import ./base.bend as LB
import ../cvar/cvar_ffi_is_expand.bend as PIE
import ../cvar/alias_expand_exact.bend as PAE

def CvarEntry.cvar_ffi_spelled(as, cs, h):
  %LB.cve.put_xreq(as, cs, "") : {FCv.ffi(_) == CvarEntry.cvs_spell_exp(Cvar.spec_expand(cs, as), "") : String}
  %Equal.sym(String, FCv.ffi(FCv.put_xreq(FCv.Xreq{as, cs}, "")), FCv.put_exp(Cv.expand(cs, as), ""), Cvar.cvar_ffi_is_expand(as, cs, h)) : {_ == CvarEntry.cvs_spell_exp(Cvar.spec_expand(cs, as), "") : String}
  %PAE.pxx.expand_orig(cs, as) : {FCv.put_exp(Cv.expand(cs, as), "") == CvarEntry.cvs_spell_exp(_, "") : String}
  LB.cve.exp(Cv.expand(cs, as), "")

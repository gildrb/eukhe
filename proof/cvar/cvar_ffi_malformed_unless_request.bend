# eukhe: the proof of LAW cvar_ffi_malformed_unless_request
#
# PROOF: whatever the entry's decoder reads is a spelled request that fits,
# then its rest (LR.cvr.xreq); when it reads none the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry
import ../wire/base/spell.bend as LAWireSpell
import ./base/read.bend as LR

def cfmu.G(+s: String) -> Type:
  &as: List<&2, Cv.Alias> -> &cs: List<&2, Cv.Cmd> -> &rest: String -> {(s, Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs))) == (CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, rest)), True{}) : String & Bool}

def cfmu.eq(+s: String, +as: List<&2, Cv.Alias>, +cs: List<&2, Cv.Cmd>, +rest: String, e1: {s == CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, rest)) : String}, e2: {Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs)) == True{} : Bool}) -> {(s, Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs))) == (CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, rest)), True{}) : String & Bool}:
  %Equal.sym(String, s, CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, rest)), e1) : {(_, Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs))) == (CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, rest)), True{}) : String & Bool}
  %Equal.sym(Bool, Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs)), True{}, e2) : {(CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, rest)), _) == (CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, rest)), True{}) : String & Bool}
  {==}

def cfmu.main(+s: String, d: Wr.Dec<FCv.Xreq>, inv: LR.cvr.Xreq(s, d), other: {String.eq(FCv.ffi.go(d), Wr.err("cvar: malformed expand request")) == False{} : Bool}) -> cfmu.G(s):
  match d:
    case Wr.Got{q, +rest}:
      match q:
        case FCv.Xreq{+as, +cs}:
          (e1, e2) = inv
          (as, (cs, (rest, cfmu.eq(s, as, cs, rest, e1, e2))))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cfmu.G(s), other)

def CvarEntry.cvar_ffi_malformed_unless_request(s, other):
  cfmu.main(s, FCv.get_xreq(s), LR.cvr.xreq(s), other)

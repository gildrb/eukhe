# eukhe: the proof of LAW cvar_open_malformed_unless_table
#
# PROOF: whatever the entry's decoder reads is a spelled table that fits,
# then its rest (LR.cvr.table); when it reads none the open is the refused
# state with the malformed error, which the premise excludes.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry
import ../wire/base/spell.bend as LAWireSpell
import ./base/read.bend as LR

def comu.G(+s: String) -> Type:
  &bs: List<&2, Cv.KeyBind> -> &as: List<&2, Cv.Alias> -> &rest: String -> {(s, Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as))) == (CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, rest)), True{}) : String & Bool}

def comu.eq(+s: String, +bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, +rest: String, e1: {s == CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, rest)) : String}, e2: {Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as)) == True{} : Bool}) -> {(s, Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as))) == (CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, rest)), True{}) : String & Bool}:
  %Equal.sym(String, s, CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, rest)), e1) : {(_, Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as))) == (CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, rest)), True{}) : String & Bool}
  %Equal.sym(Bool, Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as)), True{}, e2) : {(CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, rest)), _) == (CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, rest)), True{}) : String & Bool}
  {==}

def comu.main(+s: String, d: Wr.Dec<FCv.St>, inv: LR.cvr.Table(s, d), other: {CvarEntry.cvar_refused_with(FCv.open.go(d), "cvar: malformed press table") == False{} : Bool}) -> comu.G(s):
  match d:
    case Wr.Got{t, +rest}:
      match t:
        case FCv.Table{+bs, +as}:
          (e1, e2) = inv
          (bs, (as, (rest, comu.eq(s, bs, as, rest, e1, e2))))
        case FCv.Refused{}:
          Empty.absurd(comu.G(s), inv)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(comu.G(s), other)

def CvarEntry.cvar_open_malformed_unless_table(s, other):
  comu.main(s, FCv.get_table(s), LR.cvr.table(s), other)

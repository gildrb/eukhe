# eukhe: the proof of LAW cvar_ffi_reads_only_requests
#
# PROOF: whatever the entry's decoder reads is a spelled request that fits,
# then its rest (LR.cvr.xreq); an answer that is no error comes from a
# request read whole, nothing left, and is put_exp of the expansion, the
# spelled expansion (cvs.exp).

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/read.bend as LR
import ./base/spell.bend as LS

def cfro.G(s: String, a: String) -> Type:
  &as: List<&2, Cv.Alias> -> &cs: List<&2, Cv.Cmd> -> {(s, (Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs)), a)) == (CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, "")), (True{}, CvarEntry.cvar_spell_exp(Cv.expand(cs, as), ""))) : String & (Bool & String)}

def cfro.eq(+s: String, +as: List<&2, Cv.Alias>, +cs: List<&2, Cv.Cmd>, +a: String, e: {s == CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, "")) : String}, f: {Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs)) == True{} : Bool}, ea: {a == CvarEntry.cvar_spell_exp(Cv.expand(cs, as), "") : String}) -> {(s, (Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs)), a)) == (CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, "")), (True{}, CvarEntry.cvar_spell_exp(Cv.expand(cs, as), ""))) : String & (Bool & String)}:
  %Equal.sym(String, s, CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, "")), e) : {(_, (Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs)), a)) == (CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, "")), (True{}, CvarEntry.cvar_spell_exp(Cv.expand(cs, as), ""))) : String & (Bool & String)}
  %Equal.sym(Bool, Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs)), True{}, f) : {(CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, "")), (_, a)) == (CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, "")), (True{}, CvarEntry.cvar_spell_exp(Cv.expand(cs, as), ""))) : String & (Bool & String)}
  %Equal.sym(String, a, CvarEntry.cvar_spell_exp(Cv.expand(cs, as), ""), ea) : {(CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, "")), (True{}, _)) == (CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, "")), (True{}, CvarEntry.cvar_spell_exp(Cv.expand(cs, as), ""))) : String & (Bool & String)}
  {==}

def cfro.fin(+s: String, +as: List<&2, Cv.Alias>, +cs: List<&2, Cv.Cmd>, r: String, pre: {s == CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, r)) : String}, f: {Bool.and(CvarEntry.cvar_aliases_fit(as), CvarEntry.cvar_cmds_fit(cs)) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FCv.ffi.whole(FCv.Xreq{as, cs}, Wr.end(r))) == False{} : Bool}) -> cfro.G(s, FCv.ffi.whole(FCv.Xreq{as, cs}, Wr.end(r))):
  match r:
    case SNil{}:
      (as, (cs, cfro.eq(s, as, cs, FCv.put_exp(Cv.expand(cs, as), ""), pre, f, LS.cvs.exp(Cv.expand(cs, as), ""))))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(cfro.G(s, FCv.ffi.whole(FCv.Xreq{as, cs}, False{})), ok)

def cfro.main(+s: String, d: Wr.Dec<FCv.Xreq>, inv: LR.cvr.Xreq(s, d), ok: {LawsBase.wire_opens_err(FCv.ffi.go(d)) == False{} : Bool}) -> cfro.G(s, FCv.ffi.go(d)):
  match d:
    case Wr.Got{q, r}:
      match q:
        case FCv.Xreq{+as, +cs}:
          (e, f) = inv
          cfro.fin(s, as, cs, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cfro.G(s, Wr.err("cvar: malformed expand request")), ok)

def CvarEntry.cvar_ffi_reads_only_requests(s, ok):
  cfro.main(s, FCv.get_xreq(s), LR.cvr.xreq(s), ok)

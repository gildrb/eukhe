# eukhe: the proof of LAW cvar_open_reads_only_tables
#
# PROOF: whatever the entry's decoder reads is a spelled table that fits,
# then its rest (LR.cvr.table; it never reads a refused state); a reply
# that is no error comes from a table read whole, nothing left.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/read.bend as LR

def coro.G(s: String, a: FCv.St & String) -> Type:
  &bs: List<&2, Cv.KeyBind> -> &as: List<&2, Cv.Alias> -> {(s, (Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as)), a)) == (CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, "")), (True{}, (FCv.Table{bs, as}, ""))) : String & (Bool & (FCv.St & String))}

def coro.eq(+s: String, +bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, e: {s == CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, "")) : String}, f: {Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as)) == True{} : Bool}) -> {(s, (Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as)), (FCv.Table{bs, as}, ""))) == (CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, "")), (True{}, (FCv.Table{bs, as}, ""))) : String & (Bool & (FCv.St & String))}:
  %Equal.sym(String, s, CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, "")), e) : {(_, (Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as)), (FCv.Table{bs, as}, ""))) == (CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, "")), (True{}, (FCv.Table{bs, as}, ""))) : String & (Bool & (FCv.St & String))}
  %Equal.sym(Bool, Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as)), True{}, f) : {(CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, "")), (_, (FCv.Table{bs, as}, ""))) == (CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, "")), (True{}, (FCv.Table{bs, as}, ""))) : String & (Bool & (FCv.St & String))}
  {==}

def coro.fin(+s: String, +bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, r: String, pre: {s == CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, r)) : String}, f: {Bool.and(CvarEntry.cvar_binds_fit(bs), CvarEntry.cvar_aliases_fit(as)) == True{} : Bool}, ok: {LawsBase.wire_opens_err(CvarEntry.cvar_reply_of(FCv.open.whole(FCv.Table{bs, as}, Wr.end(r)))) == False{} : Bool}) -> coro.G(s, FCv.open.whole(FCv.Table{bs, as}, Wr.end(r))):
  match r:
    case SNil{}:
      (bs, (as, coro.eq(s, bs, as, pre, f)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(coro.G(s, FCv.open.whole(FCv.Table{bs, as}, False{})), ok)

def coro.main(+s: String, d: Wr.Dec<FCv.St>, inv: LR.cvr.Table(s, d), ok: {LawsBase.wire_opens_err(CvarEntry.cvar_reply_of(FCv.open.go(d))) == False{} : Bool}) -> coro.G(s, FCv.open.go(d)):
  match d:
    case Wr.Got{t, r}:
      match t:
        case FCv.Table{+bs, +as}:
          (e, f) = inv
          coro.fin(s, bs, as, r, e, f, ok)
        case FCv.Refused{}:
          Empty.absurd(coro.G(s, FCv.open.whole(FCv.Refused{}, Wr.end(r))), inv)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(coro.G(s, (FCv.Refused{}, Wr.err("cvar: malformed press table"))), ok)

def CvarEntry.cvar_open_reads_only_tables(s, ok):
  coro.main(s, FCv.get_table(s), LR.cvr.table(s), ok)

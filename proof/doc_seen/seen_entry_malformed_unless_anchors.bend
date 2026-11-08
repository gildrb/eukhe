# eukhe: the proof of LAW seen_entry_malformed_unless_anchors
#
# PROOF: spelled seen runs that fit read back with the rest untouched (the
# spec's spelling is put_list of put_iv, spell.bend; its round trip,
# seen_entry_refines), so the entry goes on to the anchors' decoder, which
# reads only spelled anchors that fit (exact.bend); when it reads none the
# entry answers the anchors' error, which the premise excludes.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../bend/ffi_doc_seen.bend as Fds
import ../../bend/wire.bend as Wr
import ../../laws/doc_seen.bend as DocSeen
import ../../laws/base.bend as LawsBase
import ../base/logic/bool.bend as LLogicBool
import ../wire/base/spell.bend as LAWireSpell
import ./seen_entry_refines.bend as PSeenEntryRefines
import ./seen_entry_answers_spelled/spell.bend as Ssp
import ./seen_entry_reads_only_requests/exact.bend as Fsx

def smua_Ex(t: String) -> Type:
  &ats: List<&2, Ds.At> -> &rest: String -> ({t == DocSeen.seen.spell_ats(ats, rest) : String} & {DocSeen.seen.AnchorsFit(ats) == True{} : Bool})

# spelled seen runs that fit read back, the rest untouched
def smua_read(+ivs: List<&2, Ds.Iv>, +t: String, +fits: {DocSeen.seen.SeenFits(ivs) == True{} : Bool}) -> {Wr.get_list(~Ds.Iv, ~Fds.get_iv, DocSeen.seen.spell_seen(ivs, t)) == Wr.Got{ivs, t} : Wr.Dec<List<&2, Ds.Iv>>}:
  %Ssp.ssp_ivs(ivs, t) : {Wr.get_list(~Ds.Iv, ~Fds.get_iv, _) == Wr.Got{ivs, t} : Wr.Dec<List<&2, Ds.Iv>>}
  PSeenEntryRefines.fsv_ivs(ivs, t, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Ds.Iv, ivs)), DocSeen.seen.IvsFit(ivs), fits), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Ds.Iv, ivs)), DocSeen.seen.IvsFit(ivs), fits))

# the premise, after the seen runs read back
def smua_move(+ivs: List<&2, Ds.Iv>, +t: String, +fits: {DocSeen.seen.SeenFits(ivs) == True{} : Bool},
  other: {String.eq(Fds.ffi(DocSeen.seen.spell_seen(ivs, t)), Wr.err("doc_seen: malformed anchors")) == False{} : Bool}) ->
  {String.eq(Fds.run.ats(ivs, Wr.get_list(~Ds.At, ~Fds.get_at, t)), Wr.err("doc_seen: malformed anchors")) == False{} : Bool}:
  Equal.trans(Bool, String.eq(Fds.run.seen(Wr.Got{ivs, t}), Wr.err("doc_seen: malformed anchors")),
    String.eq(Fds.run.seen(Wr.get_list(~Ds.Iv, ~Fds.get_iv, DocSeen.seen.spell_seen(ivs, t))), Wr.err("doc_seen: malformed anchors")), False{},
    Equal.cong(Wr.Dec<List<&2, Ds.Iv>>, Bool, d => String.eq(Fds.run.seen(d), Wr.err("doc_seen: malformed anchors")),
      Wr.Got{ivs, t}, Wr.get_list(~Ds.Iv, ~Fds.get_iv, DocSeen.seen.spell_seen(ivs, t)),
      Equal.sym(Wr.Dec<List<&2, Ds.Iv>>, Wr.get_list(~Ds.Iv, ~Fds.get_iv, DocSeen.seen.spell_seen(ivs, t)), Wr.Got{ivs, t}, smua_read(ivs, t, fits))),
    other)

def smua_main(-ivs: List<&2, Ds.Iv>, -t: String, d: Wr.Dec<List<&2, Ds.At>>, pd: Fsx.fsx_pats(t, d),
  other: {String.eq(Fds.run.ats(ivs, d), Wr.err("doc_seen: malformed anchors")) == False{} : Bool}) -> smua_Ex(t):
  match d:
    case Wr.Got{+ats, +r}:
      (ats, (r, pd))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(smua_Ex(t), other)

def DocSeen.seen_entry_malformed_unless_anchors(ivs, fits, t, other):
  smua_main(ivs, t, Wr.get_list(~Ds.At, ~Fds.get_at, t), Fsx.fsx_ats(t), smua_move(ivs, t, fits, other))

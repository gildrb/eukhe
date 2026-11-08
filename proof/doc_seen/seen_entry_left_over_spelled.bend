# eukhe: the proof of LAW seen_entry_left_over_spelled
#
# PROOF: the spec's request is the entry's put_req (spell.bend); its seen
# runs and anchors read back with the rest untouched (the round trips of
# seen_entry_refines), whose end check sees the char left and answers the
# error form.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../bend/ffi_doc_seen.bend as Fds
import ../../bend/wire.bend as Wr
import ../../laws/doc_seen.bend as DocSeen
import ../../laws/base.bend as LawsBase
import ../base/logic/bool.bend as LLogicBool
import ./seen_entry_refines.bend as PSeenEntryRefines
import ./seen_entry_answers_spelled/spell.bend as Ssp

def selo_main(+ivs: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>, +h: {DocSeen.seen.WireFits(ivs, ats) == True{} : Bool}, +r: String, +c: Char) -> {Fds.ffi(Fds.put_req(ivs, ats, SCon{c, r})) == Wr.err("doc_seen: input left over") : String}:
  +hs = LLogicBool.wr_and_l(Bool.and(LawsBase.wire_fits(List.length(&2, Ds.Iv, ivs)), DocSeen.seen.IvsFit(ivs)), Bool.and(LawsBase.wire_fits(List.length(&2, Ds.At, ats)), DocSeen.seen.AtsFit(ats)), h)
  +ha = LLogicBool.wr_and_r(Bool.and(LawsBase.wire_fits(List.length(&2, Ds.Iv, ivs)), DocSeen.seen.IvsFit(ivs)), Bool.and(LawsBase.wire_fits(List.length(&2, Ds.At, ats)), DocSeen.seen.AtsFit(ats)), h)
  +left = {SCon{c, r} : String}
  +tail = Wr.put_list(~Ds.At, ~Fds.put_at, ats, left)
  +err = Wr.err("doc_seen: input left over")
  %Equal.sym(Wr.Dec<List<&2, Ds.Iv>>, Wr.get_list(~Ds.Iv, ~Fds.get_iv, Wr.put_list(~Ds.Iv, ~Fds.put_iv, ivs, tail)), Wr.Got{ivs, tail}, PSeenEntryRefines.fsv_ivs(ivs, tail, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Ds.Iv, ivs)), DocSeen.seen.IvsFit(ivs), hs), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Ds.Iv, ivs)), DocSeen.seen.IvsFit(ivs), hs))) : {Fds.run.seen(_) == err : String}
  %Equal.sym(Wr.Dec<List<&2, Ds.At>>, Wr.get_list(~Ds.At, ~Fds.get_at, tail), Wr.Got{ats, left}, PSeenEntryRefines.fsv_ats(ats, left, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Ds.At, ats)), DocSeen.seen.AtsFit(ats), ha), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Ds.At, ats)), DocSeen.seen.AtsFit(ats), ha))) : {Fds.run.ats(ivs, _) == err : String}
  {==}

def DocSeen.seen_entry_left_over_spelled(ivs, ats, fits, c, rest):
  %Ssp.ssp_req(ivs, ats, SCon{c, rest}) : {Fds.ffi(_) == Wr.err("doc_seen: input left over") : String}
  selo_main(ivs, ats, fits, rest, c)

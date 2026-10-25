# eukhe: the proof of LAW cache_marks_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (cache_marks_entry_reads), so the entry answers the code's decision,
# which is the spec's (cache_marks_excess, cache_marks_grant), encoded as
# the spec spells it (LA.cmb.put_list for the list of Bools).

import Base
import ../../bend/cache_marks.bend as Cm
import ../../bend/ffi_cache_marks.bend as FCm
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/cache_marks.bend as CacheMarks
import ./base.bend as LA
import ./cache_marks_excess.bend as PCacheMarksExcess
import ./cache_marks_grant.bend as PCacheMarksGrant
import ./cache_marks_entry_reads.bend as PCacheMarksEntryReads

def cma.put(m: Maybe<&2, String>) -> {FCm.put_excess(m) == CacheMarks.sp_w_excess(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      {==}

def cma.reply(q: FCm.Req) -> {FCm.answer(q) == CacheMarks.sp_w_reply(q) : String}:
  match q:
    case FCm.QExcess{+n}:
      %Equal.sym(Maybe<&2, String>, Cm.excess(n), CacheMarks.sp_excess(n), CacheMarks.cache_marks_excess(n)) : {FCm.put_excess(_) == CacheMarks.sp_w_excess(CacheMarks.sp_excess(n)) : String}
      cma.put(CacheMarks.sp_excess(n))
    case FCm.QGrant{+p, +ws}:
      +g = CacheMarks.sp_grant(p, ws)
      %Equal.sym(List<&2, Bool>, Cm.grant(p, ws), g, CacheMarks.cache_marks_grant(p, ws)) : {Wr.put_list(~Bool, ~Wr.put_bool, _, "") == Wr.put_nat(List.length(&2, Bool, g), CacheMarks.sp_w_bools(g, "")) : String}
      LA.cmb.put_list(g, "")

def CacheMarks.cache_marks_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FCm.Req>, FCm.get_req(CacheMarks.sp_w_req(q, "")), Wr.Got{q, ""}, CacheMarks.cache_marks_entry_reads(q, "", h)) : {FCm.ffi.got(_) == CacheMarks.sp_w_reply(q) : String}
  cma.reply(q)

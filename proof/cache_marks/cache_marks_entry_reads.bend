# eukhe: the proof of LAW cache_marks_entry_reads
#
# PROOF: the question's tag reads back, then its counts by
# wire_nat_round_trip (they fit by the premise), then the wanted marks by
# the round trip of a list of Bools (LLog.pe.rt, after LA.cmb.put_list
# turns the spec's spelling into the list encoder's), so each stage of the
# decoder hands the next one exactly the rest after its field.

import Base
import ../../bend/cache_marks.bend as Cm
import ../../bend/ffi_cache_marks.bend as FCm
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/cache_marks.bend as CacheMarks
import ../base/logic/bool.bend as LLogicBool
import ../log/base.bend as LLog
import ./base.bend as LA

def cmr.req(q: FCm.Req, +rest: String, h: {CacheMarks.sp_fit_req(q) == True{} : Bool}) -> {FCm.get_req(CacheMarks.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FCm.Req>}:
  match q:
    case FCm.QExcess{+n}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h)) : {FCm.get_req.marked(_) == Wr.Got{FCm.QExcess{n}, rest} : Wr.Dec<FCm.Req>}
      {==}
    case FCm.QGrant{+p, +ws}:
      +hq = h
      +fp = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(p), LawsBase.wire_fits(List.length(&2, Bool, ws)), hq)
      +fn = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(p), LawsBase.wire_fits(List.length(&2, Bool, ws)), hq)
      +l = Wr.put_nat(List.length(&2, Bool, ws), CacheMarks.sp_w_bools(ws, rest))
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(p, l)), Wr.Got{p, l}, Wire.wire_nat_round_trip(p, l, fp)) : {FCm.get_req.placed(_) == Wr.Got{FCm.QGrant{p, ws}, rest} : Wr.Dec<FCm.Req>}
      %LA.cmb.put_list(ws, rest) : {FCm.get_req.wants(p, Wr.get_list(~Bool, ~Wr.get_bool, _)) == Wr.Got{FCm.QGrant{p, ws}, rest} : Wr.Dec<FCm.Req>}
      %Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_list(~Bool, ~Wr.put_bool, ws, rest)), Wr.Got{ws, rest}, LLog.pe.rt(ws, rest, fn)) : {FCm.get_req.wants(p, _) == Wr.Got{FCm.QGrant{p, ws}, rest} : Wr.Dec<FCm.Req>}
      {==}

def CacheMarks.cache_marks_entry_reads(q, rest, h):
  cmr.req(q, rest, h)

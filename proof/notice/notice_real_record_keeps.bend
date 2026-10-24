# eukhe: the proof of LAW notice_real_record_keeps

import Base
import ../../bend/notice.bend as No
import ../../bend/ffi_notice.bend as FNo
import ../../bend/wire.bend as Wr
import ../../laws/notice.bend as Notice
import ./base.bend as LA

# a hidden restore notice stays held: the record only adds (LA.nt.held_rec)
def nrk.at(b: Bool, +rs: List<&2, No.Seen>, +sid: String, +q: String, +ms: List<&2, No.Msg>, +s: String, h: {No.visible.at(rs, q, No.notice.of(b, s)) == False{} : Bool}) -> {No.visible.at(No.record(rs, sid, ms), q, No.notice.of(b, s)) == False{} : Bool}:
  match b:
    case True{}:
      +x = Bool.and(No.same(sid, q), Notice.nt_has(ms, s))
      %Equal.sym(Bool, No.held(No.record.go(ms, sid, rs), q, s), Bool.or(x, No.held(rs, q, s)), LA.nt.held_rec(ms, sid, rs, q, s)) : {Bool.not(_) == False{} : Bool}
      %Equal.sym(Bool, No.held(rs, q, s), True{}, LA.nt.not_false(No.held(rs, q, s), h)) : {Bool.not(Bool.or(x, _)) == False{} : Bool}
      %Equal.sym(Bool, Bool.or(x, True{}), True{}, LA.nt.or_true(x)) : {Bool.not(_) == False{} : Bool}
      {==}
    case False{}:
      LA.notice.pn.absurdF({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))

def nrk.go(+rs: List<&2, No.Seen>, +sid: String, +q: String, +ms: List<&2, No.Msg>, m: No.Msg, h: {No.visible(rs, q, m) == False{} : Bool}) -> {No.visible(No.record(rs, sid, ms), q, m) == False{} : Bool}:
  match m:
    case No.Other{}:
      LA.notice.pn.absurdF({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case No.Custom{+k, +s}:
      nrk.at(No.same(k, No.restore_kind()), rs, sid, q, ms, s, h)

def Notice.notice_real_record_keeps(rs, sid, q, ms, m, h):
  nrk.go(rs, sid, q, ms, m, h)

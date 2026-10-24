# eukhe: the proof of LAW notice_real_apart

import Base
import ../../bend/notice.bend as No
import ../../bend/ffi_notice.bend as FNo
import ../../bend/wire.bend as Wr
import ../../laws/notice.bend as Notice
import ./base.bend as LA

# a record of session sid adds nothing for q: same(sid, q) is the spec's
# nt_eq (LA.nt.same_eq), False
def nra.at(b: Bool, +rs: List<&2, No.Seen>, +sid: String, +q: String, +ms: List<&2, No.Msg>, +s: String, h: {Notice.nt_eq(sid, q) == False{} : Bool}) -> {No.visible.at(No.record(rs, sid, ms), q, No.notice.of(b, s)) == No.visible.at(rs, q, No.notice.of(b, s)) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, No.held(No.record.go(ms, sid, rs), q, s), Bool.or(Bool.and(No.same(sid, q), Notice.nt_has(ms, s)), No.held(rs, q, s)), LA.nt.held_rec(ms, sid, rs, q, s)) : {Bool.not(_) == Bool.not(No.held(rs, q, s)) : Bool}
      %Equal.sym(Bool, No.same(sid, q), Notice.nt_eq(sid, q), LA.nt.same_eq(sid, q)) : {Bool.not(Bool.or(Bool.and(_, Notice.nt_has(ms, s)), No.held(rs, q, s))) == Bool.not(No.held(rs, q, s)) : Bool}
      %Equal.sym(Bool, Notice.nt_eq(sid, q), False{}, h) : {Bool.not(Bool.or(Bool.and(_, Notice.nt_has(ms, s)), No.held(rs, q, s))) == Bool.not(No.held(rs, q, s)) : Bool}
      {==}
    case False{}:
      {==}

def nra.go(+rs: List<&2, No.Seen>, +sid: String, +q: String, +ms: List<&2, No.Msg>, m: No.Msg, h: {Notice.nt_eq(sid, q) == False{} : Bool}) -> {No.visible(No.record(rs, sid, ms), q, m) == No.visible(rs, q, m) : Bool}:
  match m:
    case No.Other{}:
      {==}
    case No.Custom{+k, +s}:
      nra.at(No.same(k, No.restore_kind()), rs, sid, q, ms, s, h)

def Notice.notice_real_apart(rs, sid, q, ms, m, h):
  nra.go(rs, sid, q, ms, m, h)

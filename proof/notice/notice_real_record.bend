# eukhe: the proof of LAW notice_real_record
#
# A message of another role, or a custom message of another kind, shows
# before and after any record. A restore notice stamped s of session q is
# held after the record exactly when the record of ms for sid adds it
# (sid = q and ms holds s) or rs held it before (LA.nt.held_rec); its
# visibility is the negation, split by De Morgan.

import Base
import ../../bend/notice.bend as No
import ../../laws/notice.bend as Notice
import ./base.bend as LA

# not (x or y) is (not y) and (not x)
def nrr.dm(x: Bool, y: Bool) -> {Bool.not(Bool.or(x, y)) == Bool.and(Bool.not(y), Bool.not(x)) : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the decision on a custom message whose kind test answered b
def nrr.at(b: Bool, +rs: List<&2, No.Seen>, +sid: String, +q: String, +ms: List<&2, No.Msg>, +s: String) -> {No.visible.at(No.record(rs, sid, ms), q, No.notice.of(b, s)) == Bool.and(No.visible.at(rs, q, No.notice.of(b, s)), Bool.not(Bool.and(b, Bool.and(Notice.nt_eq(sid, q), Notice.nt_has(ms, s))))) : Bool}:
  match b:
    case True{}:
      +x = Bool.and(Notice.nt_eq(sid, q), Notice.nt_has(ms, s))
      +y = No.held(rs, q, s)
      %Equal.sym(Bool, No.held(No.record.go(ms, sid, rs), q, s), Bool.or(Bool.and(No.same(sid, q), Notice.nt_has(ms, s)), y), LA.nt.held_rec(ms, sid, rs, q, s)) : {Bool.not(_) == Bool.and(Bool.not(y), Bool.not(x)) : Bool}
      %Equal.sym(Bool, No.same(sid, q), Notice.nt_eq(sid, q), LA.nt.same_eq(sid, q)) : {Bool.not(Bool.or(Bool.and(_, Notice.nt_has(ms, s)), y)) == Bool.and(Bool.not(y), Bool.not(x)) : Bool}
      nrr.dm(x, y)
    case False{}:
      {==}

def nrr.go(+rs: List<&2, No.Seen>, +sid: String, +q: String, +ms: List<&2, No.Msg>, m: No.Msg) -> {No.visible(No.record(rs, sid, ms), q, m) == Bool.and(No.visible(rs, q, m), Bool.not(Notice.nt_hides(q, sid, m, ms))) : Bool}:
  match m:
    case No.Other{}:
      {==}
    case No.Custom{+k, +s}:
      +b = No.same(k, No.restore_kind())
      %LA.nt.same_eq(k, Notice.nt_kind()) : {No.visible.at(No.record(rs, sid, ms), q, No.notice.of(b, s)) == Bool.and(No.visible.at(rs, q, No.notice.of(b, s)), Bool.not(Bool.and(_, Bool.and(Notice.nt_eq(sid, q), Notice.nt_has(ms, s))))) : Bool}
      nrr.at(b, rs, sid, q, ms, s)

def Notice.notice_real_record(rs, sid, q, ms, m):
  nrr.go(rs, sid, q, ms, m)

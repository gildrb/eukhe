# eukhe: the proof of LAW notice_real_shown_once

import Base
import ../../bend/notice.bend as No
import ../../bend/ffi_notice.bend as FNo
import ../../bend/wire.bend as Wr
import ../../laws/notice.bend as Notice
import ./base.bend as LA

# the record holds the notice (LA.nt.held_rec): its session is the same as
# itself (LA.nt.same_refl) and the messages hold a restore notice of its stamp
def nrs.go(+rs: List<&2, No.Seen>, +sid: String, +s: String, +ms: List<&2, No.Msg>, h: {Notice.nt_has(ms, s) == True{} : Bool}) -> {No.visible(No.record(rs, sid, ms), sid, No.Custom{"ipython_state_restored", s}) == False{} : Bool}:
  %Equal.sym(Bool, No.held(No.record.go(ms, sid, rs), sid, s), Bool.or(Bool.and(No.same(sid, sid), Notice.nt_has(ms, s)), No.held(rs, sid, s)), LA.nt.held_rec(ms, sid, rs, sid, s)) : {Bool.not(_) == False{} : Bool}
  %Equal.sym(Bool, No.same(sid, sid), True{}, LA.nt.same_refl(sid)) : {Bool.not(Bool.or(Bool.and(_, Notice.nt_has(ms, s)), No.held(rs, sid, s))) == False{} : Bool}
  %Equal.sym(Bool, Notice.nt_has(ms, s), True{}, h) : {Bool.not(Bool.or(Bool.and(True{}, _), No.held(rs, sid, s))) == False{} : Bool}
  {==}

def Notice.notice_real_shown_once(rs, sid, s, ms, h):
  nrs.go(rs, sid, s, ms, h)

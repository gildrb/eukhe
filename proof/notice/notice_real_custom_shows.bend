# eukhe: the proof of LAW notice_real_custom_shows

import Base
import ../../bend/notice.bend as No
import ../../bend/ffi_notice.bend as FNo
import ../../bend/wire.bend as Wr
import ../../laws/notice.bend as Notice
import ./base.bend as LA

# the kind test is the spec's (LA.nt.same_eq): not a restore notice
def ncs.go(+rs: List<&2, No.Seen>, +sid: String, +k: String, +s: String, h: {Notice.nt_eq(k, Notice.nt_kind()) == False{} : Bool}) -> {No.visible(rs, sid, No.Custom{k, s}) == True{} : Bool}:
  %Equal.sym(Bool, No.same(k, No.restore_kind()), Notice.nt_eq(k, No.restore_kind()), LA.nt.same_eq(k, No.restore_kind())) : {No.visible.at(rs, sid, No.notice.of(_, s)) == True{} : Bool}
  %Equal.sym(Bool, Notice.nt_eq(k, Notice.nt_kind()), False{}, h) : {No.visible.at(rs, sid, No.notice.of(_, s)) == True{} : Bool}
  {==}

def Notice.notice_real_custom_shows(rs, sid, k, s, h):
  ncs.go(rs, sid, k, s, h)

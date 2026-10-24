# eukhe: the proof of LAW notice_rule_history

import Base
import ../../bend/notice.bend as No
import ../../bend/ffi_notice.bend as FNo
import ../../bend/wire.bend as Wr
import ../../laws/notice.bend as Notice
import ./base.bend as LA

def Notice.notice_rule_history(qs, sid, m):
  LA.nt.rule(qs, sid, m)

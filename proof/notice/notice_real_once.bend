# eukhe: the proof of LAW notice_real_once

import Base
import ../../bend/notice.bend as No
import ../../laws/notice.bend as Notice
import ./notice_shown_once.bend as PNoticeShownOnce
import ./notice_once_exact.bend as PNoticeOnceExact
import ./notice_real_refines.bend as PNoticeRealRefines

# the rule's counts are the model's (notice_real_refines), and the model
# shows each notice at most once (notice_shown_once, notice_once_exact)
def nro.go(+evs: List<&2, No.Ev>) -> {Notice.nt_once(Notice.nt_counts(Notice.nt_scene(evs))) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, Notice.nt_counts(Notice.nt_scene(evs)), Notice.nt_shown(No.run(evs)), Notice.notice_real_refines(evs)) : {Notice.nt_once(_) == True{} : Bool}
  %Notice.notice_once_exact(No.run(evs)) : {_ == True{} : Bool}
  Notice.notice_shown_once(evs)

def Notice.notice_real_once(evs):
  nro.go(evs)

# eukhe: the proof of LAW notice_real_per_restore

import Base
import ../../bend/notice.bend as No
import ../../laws/notice.bend as Notice
import ./notice_per_restore.bend as PNoticePerRestore
import ./notice_real_refines.bend as PNoticeRealRefines

# the rule's counts are the model's (notice_real_refines), whose sum
# after one more attach is the restores (notice_per_restore)
def nps.go(+evs: List<&2, No.Ev>) -> {Notice.nt_sum(Notice.nt_counts(Notice.nt_scene(List.append(&2, No.Ev, evs, [No.Reconnect{}])))) == Notice.nt_restores(evs) : Nat}:
  +x = List.append(&2, No.Ev, evs, [No.Reconnect{}])
  %Equal.sym(List<&2, Nat>, Notice.nt_counts(Notice.nt_scene(x)), Notice.nt_shown(No.run(x)), Notice.notice_real_refines(x)) : {Notice.nt_sum(_) == Notice.nt_restores(evs) : Nat}
  Notice.notice_per_restore(evs)

def Notice.notice_real_per_restore(evs):
  nps.go(evs)

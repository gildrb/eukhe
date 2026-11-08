# eukhe: the proof of LAW notice_real_per_restore

import Base
import ../../bend/notice.bend as No
import ../../laws/notice.bend as Notice
import ./notice_per_restore.bend as PNoticePerRestore
import ./notice_real_refines.bend as PNoticeRealRefines
import ./notice_total_exact.bend as PNoticeTotalExact
import ./notice_restores_exact.bend as PNoticeRestoresExact

# the rule's counts are the model's (notice_real_refines), whose total
# after one more attach is the restores (notice_per_restore)
def nps.go(+evs: List<&2, No.Ev>) -> {Notice.nt_sum(Notice.nt_counts(Notice.nt_scene(List.append(&2, No.Ev, evs, [No.Reconnect{}])))) == Notice.nt_restores(evs) : Nat}:
  +x = List.append(&2, No.Ev, evs, [No.Reconnect{}])
  %Equal.sym(List<&2, Nat>, Notice.nt_counts(Notice.nt_scene(x)), Notice.nt_shown(No.run(x)), Notice.notice_real_refines(x)) : {Notice.nt_sum(_) == Notice.nt_restores(evs) : Nat}
  %Notice.notice_total_exact(No.run(x)) : {_ == Notice.nt_restores(evs) : Nat}
  Equal.trans(Nat, No.total(No.run(x)), No.restores(evs), Notice.nt_restores(evs), Notice.notice_per_restore(evs), Notice.notice_restores_exact(evs))

def Notice.notice_real_per_restore(evs):
  nps.go(evs)

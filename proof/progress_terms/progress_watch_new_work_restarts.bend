# eukhe: the proof of LAW progress_watch_new_work_restarts
#
# PROOF: the poll looks with the work so far as its token; that token
# grew past the watch's (child_new_work_is_progress), so the clock is full.

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT
import ../progress/child_new_work_is_progress.bend as PChildNewWorkIsProgress
import ../../laws/progress.bend as Progress

def ProgressTerms.progress_watch_new_work_restarts(cfg, w, hist, seg, dt, ps, x, fresh, news, tok):
  +now = List.append(&2, Nat, hist, seg)
  Equal.cong(Ch.Next, Ch.Next, v => Pr.watch(ps, cfg, now, v), Ch.look(cfg, w, 1n+dt, Ch.Busy{Some{Pr.work(now)}}), Ch.Watch{Ch.W.fresh(cfg, Some{Pr.work(now)})}, Progress.child_new_work_is_progress(cfg, w, 1n+dt, hist, seg, x, fresh, news, tok))

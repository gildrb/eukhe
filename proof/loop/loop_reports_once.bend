# eukhe: the proof of LAW loop_reports_once
#
# PROOF: at every event but Enter a report leaves the loop off, and an
# off loop stays off without a report (lh.rep_step); so by induction on
# the history (lh.rep_hist) the reports are at most one from a loop that
# is on and none from one that is off.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/history.bend as LoopHistory
import ./base/history.bend as LALoopHistory

def LoopHistory.loop_reports_once(s, h, ne):
  LALoopHistory.lh.le_trans(S.reports(S.acts(h, s)), S.one_if(S.is_on(S.phase(s))), 1n,
    LALoopHistory.lh.rep_hist(h, s, ne),
    LALoopHistory.lh.one_if_le(S.is_on(S.phase(s))))

# eukhe: the proof of LAW loop_failing_run_ends
#
# PROOF: a potential (lh.pot): 3 - f iterations are possible while
# judging, one fewer in a turn, none otherwise. An unattended event with
# no turn run to its end never raises it, and an iteration lowers it by
# one (lh.pot_step, lh.halt_tired); induction (lh.fail_hist), lh.pot_le.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/history.bend as LoopHistory
import ./base/history.bend as LALoopHistory

def LoopHistory.loop_failing_run_ends(s, h, u, nr):
  LALoopHistory.lh.le_trans(S.submits(S.acts(h, s)), LALoopHistory.lh.pot(S.phase(s), S.fails(s)), Nat.sub(3n, S.fails(s)),
    LALoopHistory.lh.fail_hist(h, s, u, nr),
    LALoopHistory.lh.pot_le(S.phase(s), S.fails(s)))

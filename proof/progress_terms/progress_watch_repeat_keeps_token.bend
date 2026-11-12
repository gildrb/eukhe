# eukhe: the proof of LAW progress_watch_repeat_keeps_token
#
# PROOF: acts the child did before keep its work (pp.repeat of
# proof/progress/base.bend), so the poll looks with the token unchanged.

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT
import ../progress/base.bend as LA

def ProgressTerms.progress_watch_repeat_keeps_token(cfg, w, hist, seg, dt, ps, within):
  +now = List.append(&2, Nat, hist, seg)
  Equal.cong(Nat, Ch.Next, n => Pr.watch(ps, cfg, now, Ch.look(cfg, w, 1n+dt, Ch.Busy{Some{n}})), Pr.work(now), Pr.work(hist), LA.pp.repeat(hist, seg, within))

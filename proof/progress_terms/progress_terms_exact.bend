# eukhe: the proof of LAW progress_terms_exact

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT

def ProgressTerms.progress_terms_exact(x, xs, g, segs, cap, hist, ps, cfg, v):
  match g:
    case Pr.Go{s}:
      (Equal.sym(Bool, ProgressTerms.mem_spec(x, xs), Pr.mem(x, xs), LPT.pg.mem(x, xs)), ({==}, (Equal.sym(Pr.Goal, ProgressTerms.goal_spec(segs, cap, hist, Pr.Go{s}), Pr.goal(segs, cap, hist, Pr.Go{s}), LPT.pg.goal(segs, cap, hist, Pr.Go{s})), Equal.sym(Ch.Next, ProgressTerms.watch_spec(ps, cfg, hist, v), Pr.watch(ps, cfg, hist, v), LPT.pg.watch(ps, cfg, hist, v)))))
    case Pr.Stop{s}:
      (Equal.sym(Bool, ProgressTerms.mem_spec(x, xs), Pr.mem(x, xs), LPT.pg.mem(x, xs)), ({==}, (Equal.sym(Pr.Goal, ProgressTerms.goal_spec(segs, cap, hist, Pr.Stop{s}), Pr.goal(segs, cap, hist, Pr.Stop{s}), LPT.pg.goal(segs, cap, hist, Pr.Stop{s})), Equal.sym(Ch.Next, ProgressTerms.watch_spec(ps, cfg, hist, v), Pr.watch(ps, cfg, hist, v), LPT.pg.watch(ps, cfg, hist, v)))))

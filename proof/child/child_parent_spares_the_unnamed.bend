# eukhe: the proof of LAW child_parent_spares_the_unnamed
# The ids differ (the premise), so the act misses the submission.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun

def ChildRun.child_parent_spares_the_unnamed(cfg, ph, cut, open, i, m, other):
  %Equal.sym(Bool, Nat.is_eq(i, m), False{}, other) : {[Ch.Sub{i, Ch.Act.hit(_, Ch.Placed{})}] == [Ch.Sub{i, Ch.Queued{}}] : List<&2, Ch.Sub>} & {[Ch.Sub{i, Ch.Act.hit(_, Ch.Withdrawn{})}] == [Ch.Sub{i, Ch.Queued{}}] : List<&2, Ch.Sub>}
  ({==}, {==})

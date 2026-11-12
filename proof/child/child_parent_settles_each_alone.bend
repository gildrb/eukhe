# eukhe: the proof of LAW child_parent_settles_each_alone
# Each of the four events acts on every submission by itself
# (LAR.pcr.act_app).

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun
import ./base/run.bend as LAR

def ChildRun.child_parent_settles_each_alone(cfg, ph, cut, open, xs, ys, m):
  (LAR.pcr.act_app(xs, ys, Ch.Place{m}), (LAR.pcr.act_app(xs, ys, Ch.Pull{m}), (LAR.pcr.act_app(xs, ys, Ch.PullAll{}), LAR.pcr.act_app(xs, ys, Ch.PullAll{}))))

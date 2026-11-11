# eukhe: the proof of LAW child_parent_settles_the_named
# An id is the id it names (LAR.pcr.named); an abort and a close compute.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun
import ./base/run.bend as LAR

def ChildRun.child_parent_settles_the_named(cfg, ph, cut, open, i):
  (LAR.pcr.named(i, Ch.Placed{}), (LAR.pcr.named(i, Ch.Withdrawn{}), ({==}, {==})))

# eukhe: the proof of LAW child_read_reads_the_owed_report
# A watched child and an ended task compute; the newest submission is the
# one read (LAR.pcr.read_at), fate by fate.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun
import ./base/run.bend as LAR

def ChildRun.child_read_reads_the_owed_report(cfg, w, k, n, cut, open, inbox):
  ({==}, ({==}, (LAR.pcr.read_at(n, Ch.Queued{}, inbox), (LAR.pcr.read_at(n, Ch.Withdrawn{}, inbox), (LAR.pcr.read_at(n, Ch.Placed{}, inbox), LAR.pcr.read_at(n, Ch.Read{}, inbox))))))

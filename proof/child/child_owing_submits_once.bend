# eukhe: the proof of LAW child_owing_submits_once
# The inbox holds no submission n, so the task reads no fate
# (LAR.pcr.none); the report rule on no fate computes for an open and for
# a closing parent (po.none).

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun
import ./base/run.bend as LAR

def po.none(open: Bool, +k: Ch.Report, +n: Nat, +inbox: List<&2, Ch.Sub>) -> {Ch.St.ph(Ch.owe(None{}, k, n, open, inbox)) == ChildRun.chr_moved(Ch.owe.next(None{}, n), k, n) : Ch.Ph} & {Ch.St.inbox(Ch.owe(None{}, k, n, open, inbox)) == ChildRun.chr_sent(open, n, inbox) : List<&2, Ch.Sub>}:
  match open:
    case True{}:
      ({==}, {==})
    case False{}:
      ({==}, {==})

def ChildRun.child_owing_submits_once(cfg, k, n, open, inbox, dt, o, none):
  %Equal.sym(Maybe<&2, Ch.Fate>, Ch.fate(inbox, n), None{}, LAR.pcr.none(inbox, n, none)) : {Ch.St.ph(Ch.owe(_, k, n, open, inbox)) == ChildRun.chr_moved(Ch.owe.next(None{}, n), k, n) : Ch.Ph} & {Ch.St.inbox(Ch.owe(_, k, n, open, inbox)) == ChildRun.chr_sent(open, n, inbox) : List<&2, Ch.Sub>}
  po.none(open, k, n, inbox)

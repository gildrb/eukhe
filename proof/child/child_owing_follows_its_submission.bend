# eukhe: the proof of LAW child_owing_follows_its_submission
# The task reads the fate of the first submission n (LAR.pcr.finds); the
# report rule on each fate computes (po.some).

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun
import ./base/run.bend as LAR

def po.some(f: Ch.Fate, +k: Ch.Report, +n: Nat, +open: Bool, +inbox: List<&2, Ch.Sub>) -> {Ch.St.ph(Ch.owe(Some{f}, k, n, open, inbox)) == ChildRun.chr_moved(Ch.owe.next(Some{f}, n), k, n) : Ch.Ph} & {Ch.St.inbox(Ch.owe(Some{f}, k, n, open, inbox)) == inbox : List<&2, Ch.Sub>}:
  match f:
    case Ch.Queued{}:
      ({==}, {==})
    case Ch.Withdrawn{}:
      ({==}, {==})
    case Ch.Placed{}:
      ({==}, {==})
    case Ch.Read{}:
      ({==}, {==})

def ChildRun.child_owing_follows_its_submission(cfg, k, n, open, pre, f, rest, dt, o, newest):
  %Equal.sym(Maybe<&2, Ch.Fate>, Ch.fate(List.append(&2, Ch.Sub, pre, Ch.Sub{n, f} <> rest), n), Some{f}, LAR.pcr.finds(pre, n, f, rest, newest)) : {Ch.St.ph(Ch.owe(_, k, n, open, List.append(&2, Ch.Sub, pre, Ch.Sub{n, f} <> rest))) == ChildRun.chr_moved(Ch.owe.next(Some{f}, n), k, n) : Ch.Ph} & {Ch.St.inbox(Ch.owe(_, k, n, open, List.append(&2, Ch.Sub, pre, Ch.Sub{n, f} <> rest))) == List.append(&2, Ch.Sub, pre, Ch.Sub{n, f} <> rest) : List<&2, Ch.Sub>}
  po.some(f, k, n, open, List.append(&2, Ch.Sub, pre, Ch.Sub{n, f} <> rest))

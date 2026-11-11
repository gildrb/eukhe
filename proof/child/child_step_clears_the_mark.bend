# eukhe: the proof of LAW child_step_clears_the_mark
# State by state: the abort, the watch and an ended task compute; the
# report rule leaves no mark and the parent's openness on every fate
# (pm.owe).

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun

def pm.owe(f: Maybe<&2, Ch.Fate>, +k: Ch.Report, +n: Nat, open: Bool, +inbox: List<&2, Ch.Sub>) -> {ChildRun.chr_cut(Ch.owe(f, k, n, open, inbox)) == None{} : Maybe<&2, Bool>} & {ChildRun.chr_open(Ch.owe(f, k, n, open, inbox)) == open : Bool}:
  match f:
    case None{}:
      match open:
        case True{}:
          ({==}, {==})
        case False{}:
          ({==}, {==})
    case Some{x}:
      match x:
        case Ch.Queued{}:
          ({==}, {==})
        case Ch.Withdrawn{}:
          ({==}, {==})
        case Ch.Placed{}:
          ({==}, {==})
        case Ch.Read{}:
          ({==}, {==})

def pm.poll(cut: Maybe<&2, Bool>, ph: Ch.Ph, +open: Bool, +inbox: List<&2, Ch.Sub>, +cfg: Ch.Cfg, +dt: Nat, +o: Ch.Obs) -> {ChildRun.chr_cut(Ch.task(cfg, ph, cut, open, inbox, dt, o)) == None{} : Maybe<&2, Bool>} & {ChildRun.chr_open(Ch.task(cfg, ph, cut, open, inbox, dt, o)) == open : Bool}:
  match cut:
    case Some{d}:
      ({==}, {==})
    case None{}:
      match ph:
        case Ch.Watching{w}:
          ({==}, {==})
        case Ch.Owing{+k, +n}:
          pm.owe(Ch.fate(inbox, n), k, n, open, inbox)
        case Ch.Ended{}:
          ({==}, {==})

def pm.step(s: Ch.St, +cfg: Ch.Cfg, +dt: Nat, +o: Ch.Obs) -> {ChildRun.chr_cut(Ch.step(cfg, s, Ch.Poll{dt, o})) == None{} : Maybe<&2, Bool>} & {ChildRun.chr_open(Ch.step(cfg, s, Ch.Poll{dt, o})) == ChildRun.chr_open(s) : Bool}:
  match s:
    case Ch.St{+ph, +cut, +open, +inbox}:
      pm.poll(cut, ph, open, inbox, cfg, dt, o)

def ChildRun.child_step_clears_the_mark(cfg, s, dt, o):
  pm.step(s, cfg, dt, o)

# eukhe: the proof of LAW child_abort_runs_at_the_next_step
# With no mark and with a mark already there, the two events compute.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun

def pab.go(s: Ch.St, +cfg: Ch.Cfg, +del: Bool, +dt: Nat, +o: Ch.Obs) -> {Ch.St.ph(Ch.step(cfg, s, Ch.Cut{del})) == Ch.St.ph(s) : Ch.Ph} & ({Ch.St.ph(Ch.run([Ch.Cut{del}, Ch.Poll{dt, o}], cfg, s)) == Ch.cut.ph(Ch.St.ph(s), Bool.or(ChildRun.chr_deletes(ChildRun.chr_cut(s)), del)) : Ch.Ph} & ({Ch.St.inbox(Ch.run([Ch.Cut{del}, Ch.Poll{dt, o}], cfg, s)) == Ch.St.inbox(s) : List<&2, Ch.Sub>} & {ChildRun.chr_cut(Ch.run([Ch.Cut{del}, Ch.Poll{dt, o}], cfg, s)) == None{} : Maybe<&2, Bool>})):
  match s:
    case Ch.St{ph, cut, open, inbox}:
      match cut:
        case None{}:
          ({==}, ({==}, ({==}, {==})))
        case Some{d}:
          ({==}, ({==}, ({==}, {==})))

def ChildRun.child_abort_runs_at_the_next_step(cfg, s, del, dt, o):
  pab.go(s, cfg, del, dt, o)

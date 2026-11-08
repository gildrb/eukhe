# eukhe: the proof of LAW dir_run_step_by_step

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director

# one more step after a run is the step on the loop the run leaves
def pr.snoc(xs: List<&2, List<&2, Dr.Verdict>>, +vs: List<&2, Dr.Verdict>, +cap: Nat, +l: Dr.Loop) -> {Dr.run(List.append(&2, List<&2, Dr.Verdict>, xs, [vs]), cap, l) == Dr.tick(cap, Dr.run(xs, cap, l), vs) : Dr.Loop}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      pr.snoc(rest, vs, cap, Dr.tick(cap, l, x))

def Director.dir_run_step_by_step(xs, vs, cap, l):
  Equal.cong(Dr.Loop, Dr.Loop & Dr.Loop, y => (l, y), Dr.run(List.append(&2, List<&2, Dr.Verdict>, xs, [vs]), cap, l), Dr.tick(cap, Dr.run(xs, cap, l), vs), pr.snoc(xs, vs, cap, l))

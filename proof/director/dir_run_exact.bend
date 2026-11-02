# eukhe: the proof of LAW dir_run_exact
# Step by step: each step of the model is the spec's (dir_ffi_exact's
# lemma de.tick).

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./dir_ffi_exact.bend as PE

def pdr.run(vss: List<&2, List<&2, Dr.Verdict>>, +cap: Nat, +l: Dr.Loop) -> {Dr.run(vss, cap, l) == Director.dirs.steps(vss, cap, l) : Dr.Loop}:
  match vss:
    case Nil{}:
      {==}
    case +vs <> rest:
      %PE.de.tick(cap, l, vs) : {Dr.run(rest, cap, Dr.tick(cap, l, vs)) == Director.dirs.steps(rest, cap, _) : Dr.Loop}
      pdr.run(rest, cap, Dr.tick(cap, l, vs))

def Director.dir_run_exact(vss, cap, l):
  pdr.run(vss, cap, l)

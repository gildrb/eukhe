# eukhe: the proof of LAW roster_run_spec
# Induction on the events: each step is the spec's (roster_step_spec).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./roster_step_spec.bend as PRosterStepSpec

def prr.run(es: List<&2, Tl.Ev>, +s: Tl.Sess) -> {Tl.run(es, s) == Tools.tr_run(es, s) : Tl.Sess}:
  match es:
    case Nil{}:
      {==}
    case +e <> rest:
      %Tools.roster_step_spec(s, e) : {Tl.run(rest, Tl.step(s, e)) == Tools.tr_run(rest, _) : Tl.Sess}
      prr.run(rest, Tl.step(s, e))

def Tools.roster_run_spec(es, s):
  prr.run(es, s)

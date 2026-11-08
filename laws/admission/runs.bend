# eukhe: the laws of area admission: the runs
#
# Ad.run (the model's history, which the H3 laws of laws/admission.bend
# read) and Ad.Live.run (the live controller's) fold a history of ops.
# admission_step_exact and admission_live_step pin each op; these laws pin
# each run, for every history and every state, to the spec's op
# (laws/admission.bend `ads_step`), one op at a time, oldest first.

import Base
import ../../bend/admission.bend as Ad
import ../admission.bend as Admission

# the spec's run: the spec's op on each op of os, oldest first, from s
def ads_run(os: List<&2, Ad.Op>, s: Ad.St) -> Ad.St:
  match os:
    case Nil{}:
      s
    case o <> r:
      ads_run(r, Admission.ads_step(s, o))

# LAW admission_run_exact (H3): on every state, the model's run of every history is the spec's op on each op, one at a time, oldest first
# EXCLUDES: a run that drops, repeats, reorders or invents ops (the run of
#   the first three ops only, which passed every H3 law: the history laws
#   hold of any prefix), a run that stops at an op or ignores the state it
#   starts from
law admission_run_exact:
  for os: List<&2, Ad.Op>
  for +s: Ad.St
  {Ad.run(os, s) == ads_run(os, s) : Ad.St}

# LAW admission_live_run_exact (H3): on the live controller of every model state, a run of every history holds the live tickets of the spec's run, numbered as the spec numbers them
# EXCLUDES: a live run that drops, repeats, reorders or invents ops (the run
#   of the first three ops only, which passed admission_live_run since the
#   model's run was cut the same way), a live run that drifts from the spec
law admission_live_run_exact:
  for +os: List<&2, Ad.Op>
  for +s: Ad.St
  {Ad.Live.run(os, Admission.adl_live(s)) == Admission.adl_live(ads_run(os, s)) : Ad.Live}

# LAW admission_live_runs_are_steps (H3): on every live controller, a run is the controller's op (which admission_live_step pins) on each op, one at a time, oldest first
# EXCLUDES: a live run that drops, repeats, reorders or invents ops, or
#   runs anything but Ad.Live.step, on a controller no model state reaches
law admission_live_runs_are_steps:
  for +x: Ad.Live
  for +o: Ad.Op
  for +os: List<&2, Ad.Op>
  {Ad.Live.run(Nil{}, x) == x : Ad.Live} & {Ad.Live.run(o <> os, x) == Ad.Live.run(os, Ad.Live.step(x, o)) : Ad.Live}

# eukhe: the proof of LAW job_rewind_model_exact
# By induction on the slots: each slot is stopped exactly when the tree
# does not hold its id (membership pinned by job_model_terms_exact's lemma).

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ./job_model_terms_exact.bend as JMT

def jr.at(b: Bool, +i: Nat, +r: Bool) -> {JobStep.rewind_slot_spec(b, Jb.Slot{i, r}) == Jb.stop.at(b, Jb.Slot{i, r}) : Jb.Slot}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def jr.rw(js: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {Jb.rewind(js, keep) == JobStep.rewind_spec(js, keep) : List<&2, Jb.Slot>}:
  match js:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Jb.Slot{+i, +r}:
          %JMT.jmt.elem(keep, i) : {Jb.stop.at(_, Jb.Slot{i, r}) <> Jb.rewind(rest, keep) == JobStep.rewind_slot_spec(JobStep.elem_spec(keep, i), Jb.Slot{i, r}) <> JobStep.rewind_spec(rest, keep) : List<&2, Jb.Slot>}
          %Equal.sym(List<&2, Jb.Slot>, Jb.rewind(rest, keep), JobStep.rewind_spec(rest, keep), jr.rw(rest, keep)) : {Jb.stop.at(JobStep.elem_spec(keep, i), Jb.Slot{i, r}) <> _ == JobStep.rewind_slot_spec(JobStep.elem_spec(keep, i), Jb.Slot{i, r}) <> JobStep.rewind_spec(rest, keep) : List<&2, Jb.Slot>}
          %jr.at(JobStep.elem_spec(keep, i), i, r) : {_ <> JobStep.rewind_spec(rest, keep) == JobStep.rewind_slot_spec(JobStep.elem_spec(keep, i), Jb.Slot{i, r}) <> JobStep.rewind_spec(rest, keep) : List<&2, Jb.Slot>}
          {==}

def JobStep.job_rewind_model_exact(js, keep):
  jr.rw(js, keep)

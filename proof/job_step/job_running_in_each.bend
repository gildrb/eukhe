# eukhe: the proof of LAW job_running_in_each
# Induction on the first table: "and" regroups; one slot is its own
# check.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ./base.bend as LA

def jr.app(js: List<&2, Jb.Slot>, +ks: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {Jb.running_in(List.append(&2, Jb.Slot, js, ks), keep) == Bool.and(Jb.running_in(js, keep), Jb.running_in(ks, keep)) : Bool}:
  match js:
    case Nil{}:
      {==}
    case +s <> rest:
      +c = Bool.or(Bool.not(Jb.Slot.running(s)), Jb.elem(keep, Jb.Slot.id(s)))
      %Equal.sym(Bool, Jb.running_in(List.append(&2, Jb.Slot, rest, ks), keep), Bool.and(Jb.running_in(rest, keep), Jb.running_in(ks, keep)), jr.app(rest, ks, keep)) : {Bool.and(c, _) == Bool.and(Bool.and(c, Jb.running_in(rest, keep)), Jb.running_in(ks, keep)) : Bool}
      LA.js.and_assoc(c, Jb.running_in(rest, keep), Jb.running_in(ks, keep))

def JobStep.job_running_in_each(js, ks, keep, i):
  (jr.app(js, ks, keep), ({==}, ({==}, LA.js.and_t(Jb.elem(keep, i)))))

# eukhe: the proof of LAW job_rewind_keeps_target_jobs
# The kills are the model's rewind (job_rewind_refines), which keeps every
# job of the target tree (rewind_keeps_target_jobs).

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ./job_rewind_refines.bend as PJobRewindRefines
import ./rewind_keeps_target_jobs.bend as PRewindKeepsTargetJobs

def Job.job_rewind_keeps_target_jobs(js, target):
  %Equal.sym(List<&2, Jb.Slot>, Job.rw_stopped(Job.rw_slots(js, 0n), Jb.kills(js, target)), Jb.rewind(Job.rw_slots(js, 0n), Job.rw_held_ids(js, target, 0n)), Job.job_rewind_refines(js, target)) : {Jb.kept(_, Job.rw_slots(js, 0n), Job.rw_held_ids(js, target, 0n)) == True{} : Bool}
  Job.rewind_keeps_target_jobs(Job.rw_slots(js, 0n), Job.rw_held_ids(js, target, 0n))

# eukhe: the proof of LAW job_rewind_stops_orphans
# The kills are the model's rewind (job_rewind_refines), which stops every
# orphan (rewind_stops_orphans).

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ./job_rewind_refines.bend as PJobRewindRefines
import ./rewind_stops_orphans.bend as PRewindStopsOrphans

def Job.job_rewind_stops_orphans(js, target):
  %Equal.sym(List<&2, Jb.Slot>, Job.rw_stopped(Job.rw_slots(js, 0n), Jb.kills(js, target)), Jb.rewind(Job.rw_slots(js, 0n), Job.rw_held_ids(js, target, 0n)), Job.job_rewind_refines(js, target)) : {Jb.running_in(_, Job.rw_held_ids(js, target, 0n)) == True{} : Bool}
  Job.rewind_stops_orphans(Job.rw_slots(js, 0n), Job.rw_held_ids(js, target, 0n))

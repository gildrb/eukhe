# eukhe: the proof of LAW job_entry_left_over
# The whole request reads back (the round trips); the input after it is
# not empty, so the entry answers the input left over.

import Base
import ../../bend/ffi_job.bend as FJb
import ../../bend/ffi_job_rewind.bend as FJr
import ../../bend/job.bend as Jb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/job.bend as Job
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ./job_entry.bend as PJobEntry
import ./job_entry_answers.bend as PJobEntryAnswers

def Job.job_entry_left_over(t, cap, j, e, x, r, ht, hc, hj, he):
  %PJobEntryAnswers.je.ev(e, SCon{x, r}) : {FJb.ffi(Wr.put_nat(t, Job.job_spell_cap(cap, Job.job_spell_job(j, _)))) == Wr.err("job: input left over") : String}
  %PJobEntryAnswers.je.job(j, FJb.put_ev(e, SCon{x, r})) : {FJb.ffi(Wr.put_nat(t, Job.job_spell_cap(cap, _))) == Wr.err("job: input left over") : String}
  %PJobEntryAnswers.je.cap(cap, FJb.put_job(j, FJb.put_ev(e, SCon{x, r}))) : {FJb.ffi(Wr.put_nat(t, _)) == Wr.err("job: input left over") : String}
  %LWire.pw6.nat(t, FJb.put_cap(cap, FJb.put_job(j, FJb.put_ev(e, SCon{x, r}))), ht) : {FJb.run.t(_) == Wr.err("job: input left over") : String}
  %PJobEntry.pw6.cap(cap, FJb.put_job(j, FJb.put_ev(e, SCon{x, r})), hc) : {FJb.run.cap(t, _) == Wr.err("job: input left over") : String}
  %PJobEntry.pw6.job(j, FJb.put_ev(e, SCon{x, r}), hj) : {FJb.run.job(t, cap, _) == Wr.err("job: input left over") : String}
  %PJobEntry.pw6.ev(e, SCon{x, r}, he) : {FJb.run.ev(t, cap, j, _) == Wr.err("job: input left over") : String}
  {==}

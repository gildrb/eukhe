# eukhe: the proof of LAW job_entry_bad_job
# The bound and the cap read back (the round trips); a job the entry
# reads is spelled and fits (base/entry.bend), which the premise rules
# out.

import Base
import ../../bend/ffi_job.bend as FJb
import ../../bend/ffi_job_rewind.bend as FJr
import ../../bend/job.bend as Jb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/job.bend as Job
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ./base/entry.bend as JER
import ./job_entry.bend as PJobEntry
import ./job_entry_answers.bend as PJobEntryAnswers

def jbj.go(-t: Nat, -cap: Maybe<&2, Nat>, -r: String, d: Wr.Dec<Jb.J>, rp: JER.jer.JobRP(r, d), no: @j: Jb.J -> @q: String -> {Job.wire_job_fits(j) == True{} : Bool} -> {r == Job.job_spell_job(j, q) : String} -> Empty) -> {FJb.run.job(t, cap, d) == Wr.err("job: bad job") : String}:
  match d:
    case Wr.Got{+j, +q}:
      (f, e) = rp
      Empty.absurd({FJb.run.job(t, cap, Wr.Got{j, q}) == Wr.err("job: bad job") : String}, no(j, q, f, e))
    case Wr.Bad{}:
      {==}

def Job.job_entry_bad_job(t, cap, r, ht, hc, no):
  %PJobEntryAnswers.je.cap(cap, r) : {FJb.ffi(Wr.put_nat(t, _)) == Wr.err("job: bad job") : String}
  %LWire.pw6.nat(t, FJb.put_cap(cap, r), ht) : {FJb.run.t(_) == Wr.err("job: bad job") : String}
  %PJobEntry.pw6.cap(cap, r, hc) : {FJb.run.cap(t, _) == Wr.err("job: bad job") : String}
  jbj.go(t, cap, r, FJb.get_job(r), JER.jer.job(r), no)

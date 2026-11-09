# eukhe: the proof of LAW job_entry_bad_event
# The bound, the cap and the job read back (the round trips); an event the
# entry reads is spelled and fits (base/entry.bend), which the premise
# rules out.

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

def jbe.go(-t: Nat, -cap: Maybe<&2, Nat>, -j: Jb.J, -r: String, d: Wr.Dec<Jb.JEv>, rp: JER.jer.EvRP(r, d), no: @e: Jb.JEv -> @q: String -> {Job.wire_ev_fits(e) == True{} : Bool} -> {r == Job.job_spell_ev(e, q) : String} -> Empty) -> {FJb.run.ev(t, cap, j, d) == Wr.err("job: bad event") : String}:
  match d:
    case Wr.Got{+e, +q}:
      (f, x) = rp
      Empty.absurd({FJb.run.ev(t, cap, j, Wr.Got{e, q}) == Wr.err("job: bad event") : String}, no(e, q, f, x))
    case Wr.Bad{}:
      {==}

def Job.job_entry_bad_event(t, cap, j, r, ht, hc, hj, no):
  %PJobEntryAnswers.je.job(j, r) : {FJb.ffi(Wr.put_nat(t, Job.job_spell_cap(cap, _))) == Wr.err("job: bad event") : String}
  %PJobEntryAnswers.je.cap(cap, FJb.put_job(j, r)) : {FJb.ffi(Wr.put_nat(t, _)) == Wr.err("job: bad event") : String}
  %LWire.pw6.nat(t, FJb.put_cap(cap, FJb.put_job(j, r)), ht) : {FJb.run.t(_) == Wr.err("job: bad event") : String}
  %PJobEntry.pw6.cap(cap, FJb.put_job(j, r), hc) : {FJb.run.cap(t, _) == Wr.err("job: bad event") : String}
  %PJobEntry.pw6.job(j, r, hj) : {FJb.run.job(t, cap, _) == Wr.err("job: bad event") : String}
  jbe.go(t, cap, j, r, FJb.get_ev(r), JER.jer.ev(r), no)

# eukhe: the proof of LAW job_entry_bad_cap
# The bound reads back (the round trip); a cap the entry reads is spelled
# and fits (base/entry.bend), which the premise rules out.

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

def jbc.go(-t: Nat, -r: String, d: Wr.Dec<Maybe<&2, Nat>>, rp: JER.jer.CapRP(r, d), no: @c: Maybe<&2, Nat> -> @q: String -> {LawsBase.wire_mfits(c) == True{} : Bool} -> {r == Job.job_spell_cap(c, q) : String} -> Empty) -> {FJb.run.cap(t, d) == Wr.err("job: bad cap") : String}:
  match d:
    case Wr.Got{+c, +q}:
      (f, e) = rp
      Empty.absurd({FJb.run.cap(t, Wr.Got{c, q}) == Wr.err("job: bad cap") : String}, no(c, q, f, e))
    case Wr.Bad{}:
      {==}

def Job.job_entry_bad_cap(t, r, ht, no):
  %LWire.pw6.nat(t, r, ht) : {FJb.run.t(_) == Wr.err("job: bad cap") : String}
  jbc.go(t, r, FJb.get_cap(r), JER.jer.cap(r), no)

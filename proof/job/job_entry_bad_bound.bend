# eukhe: the proof of LAW job_entry_bad_bound
# The entry reads a number first; one it reads is spelled (wire_nat_exact)
# and fits (wire_nat_decoded_fits), which the premise rules out; so it
# reads none and answers the bad bound.

import Base
import ../../bend/ffi_job.bend as FJb
import ../../bend/ffi_job_rewind.bend as FJr
import ../../bend/job.bend as Jb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/job.bend as Job
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits

def jbb.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, no: @t: Nat -> @r: String -> {LawsBase.wire_fits(t) == True{} : Bool} -> {s == Wr.put_nat(t, r) : String} -> Empty) -> {FJb.run.t(d) == Wr.err("job: bad bound") : String}:
  match d:
    case Wr.Got{+t, +r}:
      +e = ed
      Empty.absurd({FJb.run.t(Wr.Got{t, r}) == Wr.err("job: bad bound") : String}, no(t, r, Wire.wire_nat_decoded_fits(s, t, r, e), Wire.wire_nat_exact(s, t, r, e)))
    case Wr.Bad{}:
      {==}

def Job.job_entry_bad_bound(s, no):
  jbb.go(s, Wr.get_nat(s), {==}, no)

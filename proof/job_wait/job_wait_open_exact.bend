# eukhe: the proof of LAW job_wait_open_exact
# The open reads one Nat with the wire's decoder: a Nat decoded is its
# spelling (wire_nat_exact) and fits (wire_nat_decoded_fits); input left
# after it, or no Nat, opens the refused state, whose reply is the error
# form, against the premise.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/job_wait.bend as JobWait
import ../base/staging.bend as LStg
import ./base.bend as JWB
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits

def jwo.top(+i: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(i) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(JobWait.jw_reply(FJw.open.go(d))) == False{} : Bool}) -> Sigma<&1, &1, Nat, b => {i == Wr.put_nat(b, "") : String} & {LawsBase.wire_fits(b) == True{} : Bool}>:
  match d:
    case Wr.Got{+b, s}:
      match s:
        case SNil{}:
          +e2 = ed
          (b, (Wire.wire_nat_exact(i, b, "", e2), Wire.wire_nat_decoded_fits(i, b, "", e2)))
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, Nat, b2 => {i == Wr.put_nat(b2, "") : String} & {LawsBase.wire_fits(b2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, Nat, b2 => {i == Wr.put_nat(b2, "") : String} & {LawsBase.wire_fits(b2) == True{} : Bool}>, ok)

def JobWait.job_wait_open_exact(i, ok):
  jwo.top(i, Wr.get_nat(i), {==}, ok)

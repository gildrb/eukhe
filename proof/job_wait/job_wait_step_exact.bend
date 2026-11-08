# eukhe: the proof of LAW job_wait_step_exact
# The step reads one tag with the wire's decoder: a Nat decoded is its
# spelling (wire_nat_exact); a tag past 1, input left after it, or no
# Nat answers the error form, against the premise.

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

def jws.top(+i: String, +w: FJw.Wt, d: Wr.Dec<Nat>, ed: {Wr.get_nat(i) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(JobWait.jw_reply(FJw.step.go(w, d))) == False{} : Bool}) -> Sigma<&1, &1, Nat, t2 => {i == Wr.put_nat(t2, "") : String} & {Nat.is_lt(t2, 2n) == True{} : Bool}>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          match s:
            case SNil{}:
              (0n, (Wire.wire_nat_exact(i, 0n, "", ed), {==}))
            case SCon{x, y}:
              LStg.stg.absurd(Sigma<&1, &1, Nat, t2 => {i == Wr.put_nat(t2, "") : String} & {Nat.is_lt(t2, 2n) == True{} : Bool}>, ok)
        case 1n:
          match s:
            case SNil{}:
              (1n, (Wire.wire_nat_exact(i, 1n, "", ed), {==}))
            case SCon{x, y}:
              LStg.stg.absurd(Sigma<&1, &1, Nat, t2 => {i == Wr.put_nat(t2, "") : String} & {Nat.is_lt(t2, 2n) == True{} : Bool}>, ok)
        case 2n+p:
          match s:
            case SNil{}:
              LStg.stg.absurd(Sigma<&1, &1, Nat, t2 => {i == Wr.put_nat(t2, "") : String} & {Nat.is_lt(t2, 2n) == True{} : Bool}>, ok)
            case SCon{x, y}:
              LStg.stg.absurd(Sigma<&1, &1, Nat, t2 => {i == Wr.put_nat(t2, "") : String} & {Nat.is_lt(t2, 2n) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, Nat, t2 => {i == Wr.put_nat(t2, "") : String} & {Nat.is_lt(t2, 2n) == True{} : Bool}>, ok)

def JobWait.job_wait_step_exact(w, i, ok):
  jws.top(i, w, Wr.get_nat(i), {==}, ok)

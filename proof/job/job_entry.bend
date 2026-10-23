# eukhe: the proof of LAW job_entry

import Base
import ../../bend/ffi_job.bend as FJb
import ../../bend/job.bend as Jb
import ../../bend/wire.bend as Wr
import ../../laws/job.bend as Job
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ../wire/wire_u32_round_trip.bend as PWireU32RoundTrip

def pw6.u32(+x: U32, +rest: String) -> {Wr.Got{x, rest} == Wr.get_u32(Wr.put_u32(x, rest)) : Wr.Dec<U32>}:
  Equal.sym(Wr.Dec<U32>, Wr.get_u32(Wr.put_u32(x, rest)), Wr.Got{x, rest}, Wire.wire_u32_round_trip(x, rest))

# Job
# ---

def pw6.cap(m: Maybe<&2, Nat>, +rest: String, +h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FJb.get_cap(FJb.put_cap(m, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == FJb.get_cap.go(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+x}:
      %LWire.pw6.nat(1n, Wr.put_nat(x, rest), {==}) : {Wr.Got{Some{x}, rest} == FJb.get_cap.go(_) : Wr.Dec<Maybe<&2, Nat>>}
      %LWire.pw6.nat(x, rest, h) : {Wr.Got{Some{x}, rest} == FJb.get_cap.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def pw6.code(c: Jb.Code, +rest: String) -> {Wr.Got{c, rest} == FJb.get_code(FJb.put_code(c, rest)) : Wr.Dec<Jb.Code>}:
  match c:
    case Jb.Code{+hi, +lo}:
      %pw6.u32(hi, Wr.put_u32(lo, rest)) : {Wr.Got{Jb.Code{hi, lo}, rest} == FJb.get_code.hi(_) : Wr.Dec<Jb.Code>}
      %pw6.u32(lo, rest) : {Wr.Got{Jb.Code{hi, lo}, rest} == FJb.get_code.lo(hi, _) : Wr.Dec<Jb.Code>}
      {==}

def pw6.end(e: Jb.End, +rest: String) -> {Wr.Got{e, rest} == FJb.get_end(FJb.put_end(e, rest)) : Wr.Dec<Jb.End>}:
  match e:
    case Jb.Exited{+c}:
      %LWire.pw6.nat(0n, FJb.put_code(c, rest), {==}) : {Wr.Got{Jb.Exited{c}, rest} == FJb.get_end.go(_) : Wr.Dec<Jb.End>}
      %pw6.code(c, rest) : {Wr.Got{Jb.Exited{c}, rest} == FJb.get_end.code(_) : Wr.Dec<Jb.End>}
      {==}
    case Jb.Killed{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Jb.Killed{}, rest} == FJb.get_end.go(_) : Wr.Dec<Jb.End>}
      {==}

def pw6.job(j: Jb.J, +rest: String, +h: {Job.wire_job_fits(j) == True{} : Bool}) -> {Wr.Got{j, rest} == FJb.get_job(FJb.put_job(j, rest)) : Wr.Dec<Jb.J>}:
  match j:
    case Jb.Live{+k, +d}:
      %LWire.pw6.nat(0n, Wr.put_nat(k, Wr.put_nat(d, rest)), {==}) : {Wr.Got{Jb.Live{k, d}, rest} == FJb.get_job.go(_) : Wr.Dec<Jb.J>}
      %LWire.pw6.nat(k, Wr.put_nat(d, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(k), LawsBase.wire_fits(d), h)) : {Wr.Got{Jb.Live{k, d}, rest} == FJb.get_job.k(_) : Wr.Dec<Jb.J>}
      %LWire.pw6.nat(d, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(k), LawsBase.wire_fits(d), h)) : {Wr.Got{Jb.Live{k, d}, rest} == FJb.get_job.d(k, _) : Wr.Dec<Jb.J>}
      {==}
    case Jb.Ended{+k, +d, +x}:
      %LWire.pw6.nat(1n, Wr.put_nat(k, Wr.put_nat(d, FJb.put_end(x, rest))), {==}) : {Wr.Got{Jb.Ended{k, d, x}, rest} == FJb.get_job.go(_) : Wr.Dec<Jb.J>}
      %LWire.pw6.nat(k, Wr.put_nat(d, FJb.put_end(x, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(k), LawsBase.wire_fits(d), h)) : {Wr.Got{Jb.Ended{k, d, x}, rest} == FJb.get_job.ek(_) : Wr.Dec<Jb.J>}
      %LWire.pw6.nat(d, FJb.put_end(x, rest), LLogicBool.wr_and_r(LawsBase.wire_fits(k), LawsBase.wire_fits(d), h)) : {Wr.Got{Jb.Ended{k, d, x}, rest} == FJb.get_job.ed(k, _) : Wr.Dec<Jb.J>}
      %pw6.end(x, rest) : {Wr.Got{Jb.Ended{k, d, x}, rest} == FJb.get_job.e(k, d, _) : Wr.Dec<Jb.J>}
      {==}

def pw6.ev(e: Jb.JEv, +rest: String, +h: {Job.wire_ev_fits(e) == True{} : Bool}) -> {Wr.Got{e, rest} == FJb.get_ev(FJb.put_ev(e, rest)) : Wr.Dec<Jb.JEv>}:
  match e:
    case Jb.Out{+n}:
      %LWire.pw6.nat(0n, Wr.put_nat(n, rest), {==}) : {Wr.Got{Jb.Out{n}, rest} == FJb.get_ev.go(_) : Wr.Dec<Jb.JEv>}
      %LWire.pw6.nat(n, rest, h) : {Wr.Got{Jb.Out{n}, rest} == FJb.get_ev.out(_) : Wr.Dec<Jb.JEv>}
      {==}
    case Jb.Quit{+c}:
      %LWire.pw6.nat(1n, FJb.put_code(c, rest), {==}) : {Wr.Got{Jb.Quit{c}, rest} == FJb.get_ev.go(_) : Wr.Dec<Jb.JEv>}
      %pw6.code(c, rest) : {Wr.Got{Jb.Quit{c}, rest} == FJb.get_ev.quit(_) : Wr.Dec<Jb.JEv>}
      {==}
    case Jb.Kill{}:
      %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Jb.Kill{}, rest} == FJb.get_ev.go(_) : Wr.Dec<Jb.JEv>}
      {==}
    case Jb.Tick{}:
      %LWire.pw6.nat(3n, rest, {==}) : {Wr.Got{Jb.Tick{}, rest} == FJb.get_ev.go(_) : Wr.Dec<Jb.JEv>}
      {==}

def Job.job_entry(t, cap, j, e, ht, hc, hj, he):
  +R = FJb.put_reply(Jb.feed(t, cap, j, e), Jb.ends.of(j, e))
  %LWire.pw6.nat(t, FJb.put_cap(cap, FJb.put_job(j, FJb.put_ev(e, ""))), ht) : {FJb.run.t(_) == R : String}
  %pw6.cap(cap, FJb.put_job(j, FJb.put_ev(e, "")), hc) : {FJb.run.cap(t, _) == R : String}
  %pw6.job(j, FJb.put_ev(e, ""), hj) : {FJb.run.job(t, cap, _) == R : String}
  %pw6.ev(e, "", he) : {FJb.run.ev(t, cap, j, _) == R : String}
  {==}

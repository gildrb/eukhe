# eukhe: the proof of LAW job_entry_malformed_exact
# The entry reads every input as the laws' reader does (one lemma per
# stage, each a case split on the stage's input); at the first stage that
# does not read, both answer the same text; a whole request with input
# left over answers "job: input left over".

import Base
import ../../bend/ffi_job.bend as FJb
import ../../bend/job.bend as Jb
import ../../bend/wire.bend as Wr
import ../../laws/job.bend as Job
import ../base/logic/logic.bend as LLogicLogic

# The reader, stage by stage
# --------------------------

def jm.code_lo(+hi: U32, r: Wr.Dec<U32>) -> {Job.job_read_code.lo(hi, r) == FJb.get_code.lo(hi, r) : Wr.Dec<Jb.Code>}:
  match r:
    case Wr.Got{lo, s}:
      {==}
    case Wr.Bad{}:
      {==}

def jm.code(r: Wr.Dec<U32>) -> {Job.job_read_code(r) == FJb.get_code.hi(r) : Wr.Dec<Jb.Code>}:
  match r:
    case Wr.Got{+hi, s}:
      jm.code_lo(hi, Wr.get_u32(s))
    case Wr.Bad{}:
      {==}

def jm.end_code(r: Wr.Dec<Jb.Code>) -> {Job.job_read_end.code(r) == FJb.get_end.code(r) : Wr.Dec<Jb.End>}:
  match r:
    case Wr.Got{c, s}:
      {==}
    case Wr.Bad{}:
      {==}

def jm.end_tag(t: Nat, +s: String) -> {Job.job_read_end.tag(t, s) == FJb.get_end.tag(t, s) : Wr.Dec<Jb.End>}:
  match t:
    case 0n:
      %jm.code(Wr.get_u32(s)) : {Job.job_read_end.code(Job.job_read_code(Wr.get_u32(s))) == FJb.get_end.code(_) : Wr.Dec<Jb.End>}
      jm.end_code(Job.job_read_code(Wr.get_u32(s)))
    case 1n:
      {==}
    case 2n+p:
      {==}

def jm.end(r: Wr.Dec<Nat>) -> {Job.job_read_end(r) == FJb.get_end.go(r) : Wr.Dec<Jb.End>}:
  match r:
    case Wr.Got{t, s}:
      jm.end_tag(t, s)
    case Wr.Bad{}:
      {==}

def jm.live_d(+k: Nat, r: Wr.Dec<Nat>) -> {Job.job_read_live.d(k, r) == FJb.get_job.d(k, r) : Wr.Dec<Jb.J>}:
  match r:
    case Wr.Got{d, s}:
      {==}
    case Wr.Bad{}:
      {==}

def jm.live(r: Wr.Dec<Nat>) -> {Job.job_read_live(r) == FJb.get_job.k(r) : Wr.Dec<Jb.J>}:
  match r:
    case Wr.Got{+k, s}:
      jm.live_d(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def jm.ended_x(+k: Nat, +d: Nat, r: Wr.Dec<Jb.End>) -> {Job.job_read_ended.x(k, d, r) == FJb.get_job.e(k, d, r) : Wr.Dec<Jb.J>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def jm.ended_d(+k: Nat, r: Wr.Dec<Nat>) -> {Job.job_read_ended.d(k, r) == FJb.get_job.ed(k, r) : Wr.Dec<Jb.J>}:
  match r:
    case Wr.Got{+d, +s}:
      %jm.end(Wr.get_nat(s)) : {Job.job_read_ended.x(k, d, Job.job_read_end(Wr.get_nat(s))) == FJb.get_job.e(k, d, _) : Wr.Dec<Jb.J>}
      jm.ended_x(k, d, Job.job_read_end(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def jm.ended(r: Wr.Dec<Nat>) -> {Job.job_read_ended(r) == FJb.get_job.ek(r) : Wr.Dec<Jb.J>}:
  match r:
    case Wr.Got{+k, s}:
      jm.ended_d(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def jm.job_tag(t: Nat, s: String) -> {Job.job_read_job.tag(t, s) == FJb.get_job.tag(t, s) : Wr.Dec<Jb.J>}:
  match t:
    case 0n:
      jm.live(Wr.get_nat(s))
    case 1n:
      jm.ended(Wr.get_nat(s))
    case 2n+p:
      {==}

def jm.job(r: Wr.Dec<Nat>) -> {Job.job_read_job(r) == FJb.get_job.go(r) : Wr.Dec<Jb.J>}:
  match r:
    case Wr.Got{t, s}:
      jm.job_tag(t, s)
    case Wr.Bad{}:
      {==}

def jm.ev_out(r: Wr.Dec<Nat>) -> {Job.job_read_ev.out(r) == FJb.get_ev.out(r) : Wr.Dec<Jb.JEv>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def jm.ev_quit(r: Wr.Dec<Jb.Code>) -> {Job.job_read_ev.quit(r) == FJb.get_ev.quit(r) : Wr.Dec<Jb.JEv>}:
  match r:
    case Wr.Got{c, s}:
      {==}
    case Wr.Bad{}:
      {==}

def jm.ev_tag(t: Nat, +s: String) -> {Job.job_read_ev.tag(t, s) == FJb.get_ev.tag(t, s) : Wr.Dec<Jb.JEv>}:
  match t:
    case 0n:
      jm.ev_out(Wr.get_nat(s))
    case 1n:
      %jm.code(Wr.get_u32(s)) : {Job.job_read_ev.quit(Job.job_read_code(Wr.get_u32(s))) == FJb.get_ev.quit(_) : Wr.Dec<Jb.JEv>}
      jm.ev_quit(Job.job_read_code(Wr.get_u32(s)))
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+p:
      {==}

def jm.ev(r: Wr.Dec<Nat>) -> {Job.job_read_ev(r) == FJb.get_ev.go(r) : Wr.Dec<Jb.JEv>}:
  match r:
    case Wr.Got{t, s}:
      jm.ev_tag(t, s)
    case Wr.Bad{}:
      {==}

def jm.cap_some(r: Wr.Dec<Nat>) -> {Job.job_read_cap.some(r) == FJb.get_cap.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def jm.cap_tag(t: Nat, s: String) -> {Job.job_read_cap.tag(t, s) == FJb.get_cap.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      jm.cap_some(Wr.get_nat(s))
    case 2n+p:
      {==}

def jm.cap(r: Wr.Dec<Nat>) -> {Job.job_read_cap(r) == FJb.get_cap.go(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      jm.cap_tag(t, s)
    case Wr.Bad{}:
      {==}

# The answer, stage by stage
# --------------------------

def jm.fend(b: Bool, -t: Nat, -cap: Maybe<&2, Nat>, -j: Jb.J, -e: Jb.JEv, no: {b == False{} : Bool}) -> {FJb.run.end(b, t, cap, j, e) == SCon{'E', SCon{' ', Job.job_why.end(b)}} : String}:
  match b:
    case True{}:
      LLogicLogic.pf.absurd_tf({FJb.run.end(True{}, t, cap, j, e) == SCon{'E', SCon{' ', Job.job_why.end(True{})}} : String}, no)
    case False{}:
      {==}

def jm.fev(-t: Nat, -cap: Maybe<&2, Nat>, -j: Jb.J, r: Wr.Dec<Jb.JEv>, no: {Job.job_reads.ev(r) == False{} : Bool}) -> {FJb.run.ev(t, cap, j, r) == SCon{'E', SCon{' ', Job.job_why.ev(r)}} : String}:
  match r:
    case Wr.Got{e, s}:
      jm.fend(Wr.end(s), t, cap, j, e, no)
    case Wr.Bad{}:
      {==}

def jm.fjob(-t: Nat, -cap: Maybe<&2, Nat>, r: Wr.Dec<Jb.J>, no: {Job.job_reads.job(r) == False{} : Bool}) -> {FJb.run.job(t, cap, r) == SCon{'E', SCon{' ', Job.job_why.job(r)}} : String}:
  match r:
    case Wr.Got{j, +s}:
      %jm.ev(Wr.get_nat(s)) : {FJb.run.ev(t, cap, j, _) == SCon{'E', SCon{' ', Job.job_why.ev(Job.job_read_ev(Wr.get_nat(s)))}} : String}
      jm.fev(t, cap, j, Job.job_read_ev(Wr.get_nat(s)), no)
    case Wr.Bad{}:
      {==}

def jm.fcap(-t: Nat, r: Wr.Dec<Maybe<&2, Nat>>, no: {Job.job_reads.cap(r) == False{} : Bool}) -> {FJb.run.cap(t, r) == SCon{'E', SCon{' ', Job.job_why.cap(r)}} : String}:
  match r:
    case Wr.Got{c, +s}:
      %jm.job(Wr.get_nat(s)) : {FJb.run.job(t, c, _) == SCon{'E', SCon{' ', Job.job_why.job(Job.job_read_job(Wr.get_nat(s)))}} : String}
      jm.fjob(t, c, Job.job_read_job(Wr.get_nat(s)), no)
    case Wr.Bad{}:
      {==}

def jm.ft(r: Wr.Dec<Nat>, no: {Job.job_reads.t(r) == False{} : Bool}) -> {FJb.run.t(r) == SCon{'E', SCon{' ', Job.job_why.t(r)}} : String}:
  match r:
    case Wr.Got{t, +s}:
      %jm.cap(Wr.get_nat(s)) : {FJb.run.cap(t, _) == SCon{'E', SCon{' ', Job.job_why.cap(Job.job_read_cap(Wr.get_nat(s)))}} : String}
      jm.fcap(t, Job.job_read_cap(Wr.get_nat(s)), no)
    case Wr.Bad{}:
      {==}

def Job.job_entry_malformed_exact(s, no):
  jm.ft(Wr.get_nat(s), no)

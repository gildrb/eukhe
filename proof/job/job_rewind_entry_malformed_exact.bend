# eukhe: the proof of LAW job_rewind_entry_malformed_exact
# The entry reads every input as the laws' reader does (one lemma per
# stage, each a case split on the stage's input); where that reader finds
# no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_job_rewind.bend as FJr
import ../../bend/job.bend as Jb
import ../../bend/wire.bend as Wr
import ../../laws/job.bend as Job
import ../base/logic/logic.bend as LLogicLogic

def rm.commit_some(r: Wr.Dec<Nat>) -> {Job.rw_read_commit.some(r) == FJr.get_commit.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rm.commit_tag(t: Nat, s: String) -> {Job.rw_read_commit.tag(t, s) == FJr.get_commit.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      rm.commit_some(Wr.get_nat(s))
    case 2n+p:
      {==}

def rm.commit(r: Wr.Dec<Nat>) -> {Job.rw_read_commit(r) == FJr.get_commit.go(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      rm.commit_tag(t, s)
    case Wr.Bad{}:
      {==}

def rm.seen_after(b: Bool, r: Wr.Dec<Maybe<&2, Nat>>) -> {Job.rw_read_seen.after(b, r) == FJr.get_seen.after(b, r) : Wr.Dec<Jb.Seen>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rm.seen(r: Wr.Dec<Bool>) -> {Job.rw_read_seen(r) == FJr.get_seen.go(r) : Wr.Dec<Jb.Seen>}:
  match r:
    case Wr.Got{+b, +s}:
      %rm.commit(Wr.get_nat(s)) : {Job.rw_read_seen.after(b, Job.rw_read_commit(Wr.get_nat(s))) == FJr.get_seen.after(b, _) : Wr.Dec<Jb.Seen>}
      rm.seen_after(b, Job.rw_read_commit(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def rm.cons(x: Jb.Seen, r: Wr.Dec<List<&2, Jb.Seen>>) -> {Job.rw_read_seens.cons(x, r) == FJr.get_seens.cons(x, r) : Wr.Dec<List<&2, Jb.Seen>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rm.seens_go(n: Nat, cur: Wr.Dec<Jb.Seen>) -> {Job.rw_read_seens.go(n, cur) == FJr.get_seens.go(n, cur) : Wr.Dec<List<&2, Jb.Seen>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+x, +s}:
          %rm.seen(Wr.get_bool(s)) : {Job.rw_read_seens.cons(x, Job.rw_read_seens.go(m, Job.rw_read_seen(Wr.get_bool(s)))) == FJr.get_seens.cons(x, FJr.get_seens.go(m, _)) : Wr.Dec<List<&2, Jb.Seen>>}
          %rm.seens_go(m, Job.rw_read_seen(Wr.get_bool(s))) : {Job.rw_read_seens.cons(x, Job.rw_read_seens.go(m, Job.rw_read_seen(Wr.get_bool(s)))) == FJr.get_seens.cons(x, _) : Wr.Dec<List<&2, Jb.Seen>>}
          rm.cons(x, Job.rw_read_seens.go(m, Job.rw_read_seen(Wr.get_bool(s))))
        case Wr.Bad{}:
          {==}

def rm.seens(r: Wr.Dec<Nat>) -> {Job.rw_read_seens(r) == FJr.get_seens(r) : Wr.Dec<List<&2, Jb.Seen>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %rm.seen(Wr.get_bool(s)) : {Job.rw_read_seens.go(m, Job.rw_read_seen(Wr.get_bool(s))) == FJr.get_seens.go(m, _) : Wr.Dec<List<&2, Jb.Seen>>}
          rm.seens_go(m, Job.rw_read_seen(Wr.get_bool(s)))
    case Wr.Bad{}:
      {==}

def rm.end(b: Bool, -target: Maybe<&2, Nat>, -js: List<&2, Jb.Seen>, no: {b == False{} : Bool}) -> {FJr.run.end(b, target, js) == SCon{'E', SCon{' ', "job_rewind: malformed request"}} : String}:
  match b:
    case True{}:
      LLogicLogic.pf.absurd_tf({FJr.run.end(True{}, target, js) == SCon{'E', SCon{' ', "job_rewind: malformed request"}} : String}, no)
    case False{}:
      {==}

def rm.jobs(-target: Maybe<&2, Nat>, r: Wr.Dec<List<&2, Jb.Seen>>, no: {Job.rw_reads.jobs(r) == False{} : Bool}) -> {FJr.run.jobs(target, r) == SCon{'E', SCon{' ', "job_rewind: malformed request"}} : String}:
  match r:
    case Wr.Got{js, s}:
      rm.end(Wr.end(s), target, js, no)
    case Wr.Bad{}:
      {==}

def rm.run(r: Wr.Dec<Maybe<&2, Nat>>, no: {Job.rw_reads.target(r) == False{} : Bool}) -> {FJr.run(r) == SCon{'E', SCon{' ', "job_rewind: malformed request"}} : String}:
  match r:
    case Wr.Got{t, +s}:
      %rm.seens(Wr.get_nat(s)) : {FJr.run.jobs(t, _) == SCon{'E', SCon{' ', "job_rewind: malformed request"}} : String}
      rm.jobs(t, Job.rw_read_seens(Wr.get_nat(s)), no)
    case Wr.Bad{}:
      {==}

def Job.job_rewind_entry_malformed_exact(s, no):
  %rm.commit(Wr.get_nat(s)) : {FJr.run(_) == SCon{'E', SCon{' ', "job_rewind: malformed request"}} : String}
  rm.run(Job.rw_read_commit(Wr.get_nat(s)), no)

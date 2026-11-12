# eukhe: the proof of LAW job_rewind_entry_refuses
# The entry answers either the kills, which open with the count (a
# number, never 'E': wire_nat_not_err), or the one error form.

import Base
import ../../bend/ffi_job.bend as FJb
import ../../bend/ffi_job_rewind.bend as FJr
import ../../bend/job.bend as Jb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/job.bend as Job
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_nat_not_err.bend as PWireNatNotErr

def jrr.end(whole: Bool, +target: Maybe<&2, Nat>, +js: List<&2, Jb.Seen>, bad: {LawsBase.wire_opens_err(FJr.run.end(whole, target, js)) == True{} : Bool}) -> {FJr.run.end(whole, target, js) == Wr.err("job_rewind: malformed request") : String}:
  match whole:
    case True{}:
      +ks = Jb.kills(js, target)
      +X = Wr.put_nat(List.length(&2, Bool, ks), FJr.put_kills.items(ks, ""))
      LLogicLogic.pf.absurd_tf({FJr.run.end(True{}, target, js) == Wr.err("job_rewind: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(X), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(X), True{}, bad), Wire.wire_nat_not_err(List.length(&2, Bool, ks), FJr.put_kills.items(ks, ""))))
    case False{}:
      {==}

def jrr.jobs(+target: Maybe<&2, Nat>, d: Wr.Dec<List<&2, Jb.Seen>>, bad: {LawsBase.wire_opens_err(FJr.run.jobs(target, d)) == True{} : Bool}) -> {FJr.run.jobs(target, d) == Wr.err("job_rewind: malformed request") : String}:
  match d:
    case Wr.Got{+js, s}:
      jrr.end(Wr.end(s), target, js, bad)
    case Wr.Bad{}:
      {==}

def jrr.run(d: Wr.Dec<Maybe<&2, Nat>>, bad: {LawsBase.wire_opens_err(FJr.run(d)) == True{} : Bool}) -> {FJr.run(d) == Wr.err("job_rewind: malformed request") : String}:
  match d:
    case Wr.Got{+target, +s}:
      jrr.jobs(target, FJr.get_seens(Wr.get_nat(s)), bad)
    case Wr.Bad{}:
      {==}

def Job.job_rewind_entry_refuses(s, bad):
  jrr.run(FJr.get_commit(s), bad)

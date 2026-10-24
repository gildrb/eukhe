# eukhe: the proof of LAW job_entry_answers
# The laws' spellers write what the entry's own encoders write, so the
# request is the one job_entry reads; its reply, spelled by the laws, is
# the entry's reply.

import Base
import ../../bend/ffi_job.bend as FJb
import ../../bend/job.bend as Jb
import ../../bend/wire.bend as Wr
import ../../laws/job.bend as Job
import ./job_entry.bend as PJobEntry

def je.code(c: Jb.Code, rest: String) -> {FJb.put_code(c, rest) == Job.job_spell_code(c, rest) : String}:
  match c:
    case Jb.Code{hi, lo}:
      {==}

def je.end(e: Jb.End, +rest: String) -> {FJb.put_end(e, rest) == Job.job_spell_end(e, rest) : String}:
  match e:
    case Jb.Exited{+c}:
      %je.code(c, rest) : {Wr.put_nat(0n, FJb.put_code(c, rest)) == Wr.put_nat(0n, _) : String}
      {==}
    case Jb.Killed{}:
      {==}

def je.job(j: Jb.J, +rest: String) -> {FJb.put_job(j, rest) == Job.job_spell_job(j, rest) : String}:
  match j:
    case Jb.Live{k, d}:
      {==}
    case Jb.Ended{+k, +d, +x}:
      %je.end(x, rest) : {Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(d, FJb.put_end(x, rest)))) == Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(d, _))) : String}
      {==}

def je.ev(e: Jb.JEv, +rest: String) -> {FJb.put_ev(e, rest) == Job.job_spell_ev(e, rest) : String}:
  match e:
    case Jb.Out{n}:
      {==}
    case Jb.Quit{+c}:
      %je.code(c, rest) : {Wr.put_nat(1n, FJb.put_code(c, rest)) == Wr.put_nat(1n, _) : String}
      {==}
    case Jb.Kill{}:
      {==}
    case Jb.Tick{}:
      {==}

def je.cap(c: Maybe<&2, Nat>, rest: String) -> {FJb.put_cap(c, rest) == Job.job_spell_cap(c, rest) : String}:
  match c:
    case None{}:
      {==}
    case Some{x}:
      {==}

def je.req(+t: Nat, +cap: Maybe<&2, Nat>, +j: Jb.J, +e: Jb.JEv) -> {FJb.put_req(t, cap, j, e) == Job.job_spell_req(t, cap, j, e) : String}:
  %je.ev(e, "") : {Wr.put_nat(t, FJb.put_cap(cap, FJb.put_job(j, FJb.put_ev(e, "")))) == Wr.put_nat(t, Job.job_spell_cap(cap, Job.job_spell_job(j, _))) : String}
  %je.job(j, FJb.put_ev(e, "")) : {Wr.put_nat(t, FJb.put_cap(cap, FJb.put_job(j, FJb.put_ev(e, "")))) == Wr.put_nat(t, Job.job_spell_cap(cap, _)) : String}
  %je.cap(cap, FJb.put_job(j, FJb.put_ev(e, ""))) : {Wr.put_nat(t, FJb.put_cap(cap, FJb.put_job(j, FJb.put_ev(e, "")))) == Wr.put_nat(t, _) : String}
  {==}

# the entry's list writer writes the count, then the ends as the laws do
def je.ends_go(es: List<&2, Jb.End>, +rest: String) -> {Wr.put_list.go(~Jb.End, ~FJb.put_end, es, rest) == (List.length(&2, Jb.End, es), Job.job_spell_ends(es, rest)) : Nat & String}:
  match es:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Jb.End, ~FJb.put_end, t, rest), (List.length(&2, Jb.End, t), Job.job_spell_ends(t, rest)), je.ends_go(t, rest)) : {Wr.put_list.step(~Jb.End, ~FJb.put_end, x, _) == (1n+List.length(&2, Jb.End, t), Job.job_spell_end(x, Job.job_spell_ends(t, rest))) : Nat & String}
      %je.end(x, Job.job_spell_ends(t, rest)) : {(1n+List.length(&2, Jb.End, t), FJb.put_end(x, Job.job_spell_ends(t, rest))) == (1n+List.length(&2, Jb.End, t), _) : Nat & String}
      {==}

def je.ends(+es: List<&2, Jb.End>, +rest: String) -> {Wr.put_nat(List.length(&2, Jb.End, es), Job.job_spell_ends(es, rest)) == Wr.put_list(~Jb.End, ~FJb.put_end, es, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Jb.End, ~FJb.put_end, es, rest), (List.length(&2, Jb.End, es), Job.job_spell_ends(es, rest)), je.ends_go(es, rest)) : {Wr.put_nat(List.length(&2, Jb.End, es), Job.job_spell_ends(es, rest)) == Wr.put_list.fin(_) : String}
  {==}

def Job.job_entry_answers(t, cap, j, e, ht, hc, hj, he):
  %je.req(t, cap, j, e) : {FJb.ffi(_) == Job.job_spell_answer(t, cap, j, e) : String}
  %Equal.sym(String, FJb.ffi(FJb.put_req(t, cap, j, e)), FJb.put_reply(Jb.feed(t, cap, j, e), Jb.ends.of(j, e)), Job.job_entry(t, cap, j, e, ht, hc, hj, he)) : {_ == Job.job_spell_answer(t, cap, j, e) : String}
  %je.ends(Jb.ends.of(j, e), "") : {FJb.put_job(Jb.feed(t, cap, j, e), _) == Job.job_spell_answer(t, cap, j, e) : String}
  je.job(Jb.feed(t, cap, j, e), Wr.put_nat(List.length(&2, Jb.End, Jb.ends.of(j, e)), Job.job_spell_ends(Jb.ends.of(j, e), "")))

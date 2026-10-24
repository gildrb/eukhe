# eukhe: the proof of LAW job_rewind_entry_answers
# The entry reads back the target and every job the laws spell (the
# wire's round trip, LWire.pw6.nat), answers the model's kills, which are
# the spec's (job_rewind_exact), and writes them as the laws spell them.

import Base
import ../../bend/ffi_job_rewind.bend as FJr
import ../../bend/job.bend as Jb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/job.bend as Job
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ./job_rewind_exact.bend as PJobRewindExact

def ra.commit(m: Maybe<&2, Nat>, +rest: String, +h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FJr.get_commit(Job.rw_spell_commit(m, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == FJr.get_commit.go(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+x}:
      %LWire.pw6.nat(1n, Wr.put_nat(x, rest), {==}) : {Wr.Got{Some{x}, rest} == FJr.get_commit.go(_) : Wr.Dec<Maybe<&2, Nat>>}
      %LWire.pw6.nat(x, rest, h) : {Wr.Got{Some{x}, rest} == FJr.get_commit.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def ra.seen(s: Jb.Seen, +rest: String, +h: {Job.rw_seens_fit([s]) == True{} : Bool}) -> {Wr.Got{s, rest} == FJr.get_seen(Job.rw_spell_seen(s, rest)) : Wr.Dec<Jb.Seen>}:
  match s:
    case Jb.Seen{r, +a}:
      match r:
        case True{}:
          %ra.commit(a, rest, LLogicBool.wr_and_l(LawsBase.wire_mfits(a), True{}, h)) : {Wr.Got{Jb.Seen{True{}, a}, rest} == FJr.get_seen.after(True{}, _) : Wr.Dec<Jb.Seen>}
          {==}
        case False{}:
          %ra.commit(a, rest, LLogicBool.wr_and_l(LawsBase.wire_mfits(a), True{}, h)) : {Wr.Got{Jb.Seen{False{}, a}, rest} == FJr.get_seen.after(False{}, _) : Wr.Dec<Jb.Seen>}
          {==}

def ra.and_t(x: Bool, h: {x == True{} : Bool}) -> {Bool.and(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      h

# one job fits when it fits in front of others
def ra.head_fit(s: Jb.Seen, -t: List<&2, Jb.Seen>, h: {Job.rw_seens_fit(s <> t) == True{} : Bool}) -> {Job.rw_seens_fit([s]) == True{} : Bool}:
  match s:
    case Jb.Seen{r, +a}:
      ra.and_t(LawsBase.wire_mfits(a), LLogicBool.wr_and_l(LawsBase.wire_mfits(a), Job.rw_seens_fit(t), h))

def ra.tail_fit(s: Jb.Seen, -t: List<&2, Jb.Seen>, h: {Job.rw_seens_fit(s <> t) == True{} : Bool}) -> {Job.rw_seens_fit(t) == True{} : Bool}:
  match s:
    case Jb.Seen{r, +a}:
      LLogicBool.wr_and_r(LawsBase.wire_mfits(a), Job.rw_seens_fit(t), h)

# the jobs after the first read back, the first one being x
def ra.seens(t: List<&2, Jb.Seen>, +x: Jb.Seen, +rest: String, +h: {Job.rw_seens_fit(x <> t) == True{} : Bool}) -> {Wr.Got{x <> t, rest} == FJr.get_seens.go(List.length(&2, Jb.Seen, t), FJr.get_seen(Job.rw_spell_seen(x, Job.rw_spell_seens(t, rest)))) : Wr.Dec<List<&2, Jb.Seen>>}:
  match t:
    case Nil{}:
      %ra.seen(x, rest, ra.head_fit(x, Nil{}, h)) : {Wr.Got{[x], rest} == FJr.get_seens.go(0n, _) : Wr.Dec<List<&2, Jb.Seen>>}
      {==}
    case +y <> +u:
      %ra.seen(x, Job.rw_spell_seen(y, Job.rw_spell_seens(u, rest)), ra.head_fit(x, y <> u, h)) : {Wr.Got{x <> y <> u, rest} == FJr.get_seens.go(1n+List.length(&2, Jb.Seen, u), _) : Wr.Dec<List<&2, Jb.Seen>>}
      %ra.seens(u, y, rest, ra.tail_fit(x, y <> u, h)) : {Wr.Got{x <> y <> u, rest} == FJr.get_seens.cons(x, _) : Wr.Dec<List<&2, Jb.Seen>>}
      {==}

def ra.items(ks: List<&2, Bool>, rest: String) -> {FJr.put_kills.items(ks, rest) == Job.rw_spell_bools(ks, rest) : String}:
  match ks:
    case Nil{}:
      {==}
    case b <> t:
      %ra.items(t, rest) : {Wr.put_bool(b, FJr.put_kills.items(t, rest)) == Wr.put_bool(b, _) : String}
      {==}

def ra.kills(+ks: List<&2, Bool>) -> {FJr.put_kills(ks) == Job.rw_spell_kills(ks) : String}:
  %ra.items(ks, "") : {Wr.put_nat(List.length(&2, Bool, ks), FJr.put_kills.items(ks, "")) == Wr.put_nat(List.length(&2, Bool, ks), _) : String}
  {==}

def ra.jobs(+target: Maybe<&2, Nat>, js: List<&2, Jb.Seen>, +hl: {LawsBase.wire_fits(List.length(&2, Jb.Seen, js)) == True{} : Bool}, +hs: {Job.rw_seens_fit(js) == True{} : Bool}) -> {FJr.run.jobs(target, FJr.get_seens(Wr.get_nat(Wr.put_nat(List.length(&2, Jb.Seen, js), Job.rw_spell_seens(js, ""))))) == Job.rw_spell_kills(Job.rw_kills_spec(js, target)) : String}:
  match js:
    case Nil{}:
      {==}
    case +x <> +u:
      %LWire.pw6.nat(1n+List.length(&2, Jb.Seen, u), Job.rw_spell_seen(x, Job.rw_spell_seens(u, "")), hl) : {FJr.run.jobs(target, FJr.get_seens(_)) == Job.rw_spell_kills(Job.rw_kills_spec(x <> u, target)) : String}
      %ra.seens(u, x, "", hs) : {FJr.run.jobs(target, _) == Job.rw_spell_kills(Job.rw_kills_spec(x <> u, target)) : String}
      %Equal.sym(List<&2, Bool>, Jb.kills(x <> u, target), Job.rw_kills_spec(x <> u, target), Job.job_rewind_exact(x <> u, target)) : {FJr.put_kills(_) == Job.rw_spell_kills(Job.rw_kills_spec(x <> u, target)) : String}
      ra.kills(Job.rw_kills_spec(x <> u, target))

def Job.job_rewind_entry_answers(target, js, fits):
  +rest = Bool.and(LawsBase.wire_fits(List.length(&2, Jb.Seen, js)), Job.rw_seens_fit(js))
  +hr = LLogicBool.wr_and_r(LawsBase.wire_mfits(target), rest, fits)
  %ra.commit(target, Wr.put_nat(List.length(&2, Jb.Seen, js), Job.rw_spell_seens(js, "")), LLogicBool.wr_and_l(LawsBase.wire_mfits(target), rest, fits)) : {FJr.run(_) == Job.rw_spell_kills(Job.rw_kills_spec(js, target)) : String}
  ra.jobs(target, js, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Jb.Seen, js)), Job.rw_seens_fit(js), hr), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Jb.Seen, js)), Job.rw_seens_fit(js), hr))

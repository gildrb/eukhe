# eukhe: the proof of LAW task_life_entry_refuses
#
# PROOF: the entry answers either a reply, which opens with a Nat (a tag,
# a state's tag, a count: wire_nat_not_err) or a Bool (the join's flag:
# wire_bool_not_err), never with 'E', or the one error form; so an answer
# that opens with 'E' is that error form.

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/task_life.bend as TaskLife
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ./base.bend as LB

def tef.st_ok(x: Tl.St, rest: String) -> {LawsBase.wire_opens_err(FTl.put_st(x, rest)) == False{} : Bool}:
  match x:
    case Tl.Pending{c}:
      Wire.wire_nat_not_err(0n, Wr.put_nat(c, rest))
    case Tl.Running{c}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(c, rest))
    case Tl.Waiting{c, p}:
      Wire.wire_nat_not_err(2n, Wr.put_nat(c, FTl.put_policy(p, rest)))
    case Tl.Completing{o}:
      Wire.wire_nat_not_err(3n, FTl.put_outcome(o, rest))
    case Tl.Terminal{o}:
      Wire.wire_nat_not_err(4n, FTl.put_outcome(o, rest))

def tef.stepped_ok(r: Result<&2, &2, Tl.Why, Tl.St>) -> {LawsBase.wire_opens_err(FTl.put_stepped(r)) == False{} : Bool}:
  match r:
    case Fail{y}:
      Wire.wire_nat_not_err(0n, FTl.put_why(y, ""))
    case Done{x}:
      Wire.wire_nat_not_err(1n, FTl.put_st(x, ""))

def tef.resumed_ok(r: Tl.St & Bool) -> {LawsBase.wire_opens_err(FTl.put_resumed(r)) == False{} : Bool}:
  (x, b) = r
  tef.st_ok(x, Wr.put_bool(b, ""))

def tef.joined_ok(r: Bool & List<&2, Bool>) -> {LawsBase.wire_opens_err(FTl.put_joined(r)) == False{} : Bool}:
  (ok, ms) = r
  Wire.wire_bool_not_err(ok, Wr.put_list(~Bool, ~Wr.put_bool, ms, ""))

def tef.mark_ok(m: Tl.Mark) -> {LawsBase.wire_opens_err(FTl.put_mark(m, "")) == False{} : Bool}:
  match m:
    case Tl.Clear{}:
      Wire.wire_nat_not_err(0n, "")
    case Tl.Restart{}:
      Wire.wire_nat_not_err(1n, "")
    case Tl.Request{}:
      Wire.wire_nat_not_err(2n, "")

def tef.marks_ok(p: Nat & String) -> {LawsBase.wire_opens_err(Wr.put_list.fin(p)) == False{} : Bool}:
  (n, s) = p
  Wire.wire_nat_not_err(n, s)

# no reply opens with 'E'
def tef.answer_ok(q: FTl.Req) -> {LawsBase.wire_opens_err(FTl.answer(q)) == False{} : Bool}:
  match q:
    case FTl.QStep{x, e}:
      tef.stepped_ok(Tl.step(x, e))
    case FTl.QResume{x}:
      tef.resumed_ok(Tl.resume(x))
    case FTl.QJoin{p, ls, fs}:
      tef.joined_ok(Tl.join(p, ls, fs))
    case FTl.QMerge{a, b}:
      tef.mark_ok(Tl.merge(a, b))
    case FTl.QCascade{x, m, rs}:
      tef.marks_ok(Wr.put_list.go(~Tl.Mark, ~FTl.put_mark, Tl.cascade(x, m, rs), ""))

def tef.refuse(d: Wr.Dec<FTl.Req>, bad: {LawsBase.wire_opens_err(FTl.ffi.got(d)) == True{} : Bool}) -> {FTl.ffi.got(d) == Wr.err("task_life: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LB.tlb.absurd_tf({FTl.answer(q) == Wr.err("task_life: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FTl.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FTl.answer(q)), True{}, bad), tef.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def TaskLife.task_life_entry_refuses(s, bad):
  tef.refuse(FTl.get_req(Wr.get_nat(s)), bad)

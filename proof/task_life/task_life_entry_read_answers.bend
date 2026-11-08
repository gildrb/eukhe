# eukhe: the proof of LAW task_life_entry_read_answers
#
# PROOF: the entry reads every input as the laws' reader does (ter.req);
# where that reader finds the whole request q, the entry answers its
# decision on the request it read, which is q (tra.some), encoded as the
# spec spells it (tlr.answer).

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/submission.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../spec/durable/task_life_wire.bend as SpW
import ../../laws/task_life.bend as TaskLife
import ./base/read.bend as LR
import ./base/entry.bend as LE

def tra.MI(m: Maybe<&2, FTl.Req>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def tra.none_some(-q: FTl.Req, -G: Type, e: {None{} == Some{q} : Maybe<&2, FTl.Req>}) -> G:
  %e : tra.MI(_, G)
  Unit{}

def tra.val(d: FTl.Req, m: Maybe<&2, FTl.Req>) -> FTl.Req:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is one to one
def tra.some(+p: FTl.Req, +q: FTl.Req, e: {Some{p} == Some{q} : Maybe<&2, FTl.Req>}) -> {q == p : FTl.Req}:
  Equal.sym(FTl.Req, p, q, Equal.cong(Maybe<&2, FTl.Req>, FTl.Req, m => tra.val(p, m), Some{p}, Some{q}, e))

def tra.end(b: Bool, +q: FTl.Req, +p: FTl.Req, got: {SpW.r_whole.end(b, p) == Some{q} : Maybe<&2, FTl.Req>}) -> {FTl.ffi.done(p, b) == SpW.w_reply(q) : String}:
  match b:
    case True{}:
      %tra.some(p, q, got) : {FTl.answer(_) == SpW.w_reply(q) : String}
      LE.tlr.answer(q)
    case False{}:
      tra.none_some(q, {FTl.ffi.done(p, False{}) == SpW.w_reply(q) : String}, got)

def tra.whole(r: Wr.Dec<FTl.Req>, +q: FTl.Req, got: {SpW.r_whole(r) == Some{q} : Maybe<&2, FTl.Req>}) -> {FTl.ffi.got(r) == SpW.w_reply(q) : String}:
  match r:
    case Wr.Got{p, +s}:
      tra.end(Wr.end(s), q, p, got)
    case Wr.Bad{}:
      tra.none_some(q, {Wr.err("task_life: malformed request") == SpW.w_reply(q) : String}, got)

def TaskLife.task_life_entry_read_answers(s, q, got):
  %Equal.sym(Wr.Dec<FTl.Req>, FTl.get_req(Wr.get_nat(s)), SpW.r_req(Wr.get_nat(s)), LR.ter.req(Wr.get_nat(s))) : {FTl.ffi.got(_) == SpW.w_reply(q) : String}
  tra.whole(SpW.r_req(Wr.get_nat(s)), q, got)

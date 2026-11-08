# eukhe: the proof of LAW task_life_entry_malformed_exact
#
# PROOF: the entry reads every input as the laws' reader does (ter.req);
# where that reader finds no whole request, the entry answers its error
# form (a request read whole contradicts the premise).

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

def tme.MI(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def tme.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : tme.MI(A, _, G)
  Unit{}

def tme.end(b: Bool, -q: FTl.Req, no: {SpW.r_whole.end(b, q) == None{} : Maybe<&2, FTl.Req>}) -> {FTl.ffi.done(q, b) == Wr.err("task_life: malformed request") : String}:
  match b:
    case True{}:
      tme.some_none(FTl.Req, q, {FTl.answer(q) == Wr.err("task_life: malformed request") : String}, no)
    case False{}:
      {==}

def tme.whole(r: Wr.Dec<FTl.Req>, no: {SpW.r_whole(r) == None{} : Maybe<&2, FTl.Req>}) -> {FTl.ffi.got(r) == Wr.err("task_life: malformed request") : String}:
  match r:
    case Wr.Got{q, +s}:
      tme.end(Wr.end(s), q, no)
    case Wr.Bad{}:
      {==}

def TaskLife.task_life_entry_malformed_exact(s, no):
  %Equal.sym(Wr.Dec<FTl.Req>, FTl.get_req(Wr.get_nat(s)), SpW.r_req(Wr.get_nat(s)), LR.ter.req(Wr.get_nat(s))) : {FTl.ffi.got(_) == Wr.err("task_life: malformed request") : String}
  tme.whole(SpW.r_req(Wr.get_nat(s)), no)

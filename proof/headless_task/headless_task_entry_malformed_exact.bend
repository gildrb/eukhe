# eukhe: the proof of LAW headless_task_entry_malformed_exact
#
# PROOF: the entry reads every input as the laws' reader does (ht.req);
# where that reader finds no whole request (it fails, or input is left
# over), the entry answers its error form, and a request read whole
# contradicts the premise.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/headless_task.bend as Ht
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/ffi_headless_task.bend as FHt
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../spec/durable/headless_task.bend as SpT
import ../../laws/headless_task.bend as HeadlessTask
import ./base.bend as LAHeadlessTask

def ht.MI(m: Maybe<&2, Ht.Facts>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def ht.some_none(-x: Ht.Facts, -G: Type, e: {Some{x} == None{} : Maybe<&2, Ht.Facts>}) -> G:
  %e : ht.MI(_, G)
  Unit{}

def ht.end(e: Bool, -f: Ht.Facts, no: {SpT.r_task_whole.end(e, f) == None{} : Maybe<&2, Ht.Facts>}) -> {FHt.ffi.done(f, e) == Wr.err("headless_task: malformed request") : String}:
  match e:
    case True{}:
      ht.some_none(f, {FHt.put_verdict(Ht.decide(f), "") == Wr.err("headless_task: malformed request") : String}, no)
    case False{}:
      {==}

def ht.whole(r: Wr.Dec<Ht.Facts>, no: {SpT.r_task_whole(r) == None{} : Maybe<&2, Ht.Facts>}) -> {FHt.ffi.got(r) == Wr.err("headless_task: malformed request") : String}:
  match r:
    case Wr.Got{f, +s}:
      ht.end(Wr.end(s), f, no)
    case Wr.Bad{}:
      {==}

def HeadlessTask.headless_task_entry_malformed_exact(s, no):
  %Equal.sym(Wr.Dec<Ht.Facts>, FHt.get_facts(s), SpT.r_task(s), LAHeadlessTask.ht.req(s)) : {FHt.ffi.got(_) == Wr.err("headless_task: malformed request") : String}
  ht.whole(SpT.r_task(s), no)

# eukhe: the proof of LAW headless_exit_entry_malformed_exact
#
# PROOF: the entry reads every input as the laws' reader does (hx.req);
# where that reader finds no whole request (it fails, or input is left
# over), the entry answers its error form, and a request read whole
# contradicts the premise.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

def hx.MI(m: Maybe<&2, Hx.Facts>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def hx.some_none(-x: Hx.Facts, -G: Type, e: {Some{x} == None{} : Maybe<&2, Hx.Facts>}) -> G:
  %e : hx.MI(_, G)
  Unit{}

def hx.end(e: Bool, -f: Hx.Facts, no: {SpW.r_exit_whole.end(e, f) == None{} : Maybe<&2, Hx.Facts>}) -> {FHx.ffi.done(f, e) == Wr.err("headless_exit: malformed request") : String}:
  match e:
    case True{}:
      hx.some_none(f, {FHx.put_verdict(Hx.decide(f), "") == Wr.err("headless_exit: malformed request") : String}, no)
    case False{}:
      {==}

def hx.whole(r: Wr.Dec<Hx.Facts>, no: {SpW.r_exit_whole(r) == None{} : Maybe<&2, Hx.Facts>}) -> {FHx.ffi.got(r) == Wr.err("headless_exit: malformed request") : String}:
  match r:
    case Wr.Got{f, +s}:
      hx.end(Wr.end(s), f, no)
    case Wr.Bad{}:
      {==}

def HeadlessExit.headless_exit_entry_malformed_exact(s, no):
  %Equal.sym(Wr.Dec<Hx.Facts>, FHx.get_facts(s), SpW.r_exit(s), LAHeadlessExit.hx.req(s)) : {FHx.ffi.got(_) == Wr.err("headless_exit: malformed request") : String}
  hx.whole(SpW.r_exit(s), no)

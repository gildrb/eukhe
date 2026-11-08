# eukhe: the proof of LAW headless_settle_entry_malformed_exact
#
# PROOF: the entry reads every input as the laws' reader does (hs.req);
# where that reader finds no whole request (it fails, or input is left
# over), the entry answers its error form, and a request read whole
# contradicts the premise.

import Base
import ../../bend/headless_settle.bend as Hs
import ../../bend/ffi_headless_settle.bend as FHs
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../laws/headless_settle.bend as HeadlessSettle
import ./base.bend as LAHeadlessSettle

def hs.MI(m: Maybe<&2, Hs.Facts>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def hs.some_none(-x: Hs.Facts, -G: Type, e: {Some{x} == None{} : Maybe<&2, Hs.Facts>}) -> G:
  %e : hs.MI(_, G)
  Unit{}

def hs.end(e: Bool, -f: Hs.Facts, no: {SpW.r_settle_whole.end(e, f) == None{} : Maybe<&2, Hs.Facts>}) -> {FHs.ffi.done(f, e) == Wr.err("headless_settle: malformed request") : String}:
  match e:
    case True{}:
      hs.some_none(f, {FHs.put_settle(Hs.settle(f), "") == Wr.err("headless_settle: malformed request") : String}, no)
    case False{}:
      {==}

def hs.whole(r: Wr.Dec<Hs.Facts>, no: {SpW.r_settle_whole(r) == None{} : Maybe<&2, Hs.Facts>}) -> {FHs.ffi.got(r) == Wr.err("headless_settle: malformed request") : String}:
  match r:
    case Wr.Got{f, +s}:
      hs.end(Wr.end(s), f, no)
    case Wr.Bad{}:
      {==}

def HeadlessSettle.headless_settle_entry_malformed_exact(s, no):
  %Equal.sym(Wr.Dec<Hs.Facts>, FHs.get_facts(s), SpW.r_settle(s), LAHeadlessSettle.hs.req(s)) : {FHs.ffi.got(_) == Wr.err("headless_settle: malformed request") : String}
  hs.whole(SpW.r_settle(s), no)

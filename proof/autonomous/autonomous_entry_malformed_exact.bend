# eukhe: the proof of LAW autonomous_entry_malformed_exact
#
# PROOF: the entry reads every input as the laws' reader does (au.req);
# where that reader finds no whole request (it fails, or input is left
# over), the entry answers its error form, and a request read whole
# contradicts the premise.

import Base
import ../../bend/verify.bend as V
import ../../bend/autonomous.bend as Au
import ../../bend/ffi_autonomous.bend as FAu
import ../../bend/wire.bend as Wr
import ../../spec/autonomous/autonomous.bend as SpA
import ../../laws/autonomous.bend as Autonomous
import ./base.bend as LAAutonomous

def au.MI(m: Maybe<&2, Au.Facts>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def au.some_none(-x: Au.Facts, -G: Type, e: {Some{x} == None{} : Maybe<&2, Au.Facts>}) -> G:
  %e : au.MI(_, G)
  Unit{}

def au.end(e: Bool, -f: Au.Facts, no: {SpA.r_whole.end(e, f) == None{} : Maybe<&2, Au.Facts>}) -> {FAu.ffi.done(f, e) == Wr.err("autonomous: malformed request") : String}:
  match e:
    case True{}:
      au.some_none(f, {FAu.put_step(Au.decide(f), "") == Wr.err("autonomous: malformed request") : String}, no)
    case False{}:
      {==}

def au.whole(r: Wr.Dec<Au.Facts>, no: {SpA.r_whole(r) == None{} : Maybe<&2, Au.Facts>}) -> {FAu.ffi.got(r) == Wr.err("autonomous: malformed request") : String}:
  match r:
    case Wr.Got{f, +s}:
      au.end(Wr.end(s), f, no)
    case Wr.Bad{}:
      {==}

def Autonomous.autonomous_entry_malformed_exact(s, no):
  %Equal.sym(Wr.Dec<Au.Facts>, FAu.get_facts(s), SpA.r_req(s), LAAutonomous.au.req(s)) : {FAu.ffi.got(_) == Wr.err("autonomous: malformed request") : String}
  au.whole(SpA.r_req(s), no)

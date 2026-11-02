# eukhe: the proof of LAW wait_any_entry_read_answers
#
# PROOF: the entry reads every input as the laws' reader does (wa.req); a
# request the reader reads whole, with nothing left, is the one the entry
# answers, and its answer is the spec's, spelled (wa.answer); a reader
# that fails or leaves input contradicts the premise.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../spec/durable/wait_any_wire.bend as SpW
import ./wait_any_entry_answers.bend as PWaitAnyEntryAnswers

def wra.MI(m: Maybe<&2, FWa.Req>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def wra.some_none(-x: FWa.Req, -G: Type, e: {Some{x} == None{} : Maybe<&2, FWa.Req>}) -> G:
  %e : wra.MI(_, G)
  Unit{}

def wra.none_some(-x: FWa.Req, -G: Type, e: {None{} == Some{x} : Maybe<&2, FWa.Req>}) -> G:
  wra.some_none(x, G, Equal.sym(Maybe<&2, FWa.Req>, None{}, Some{x}, e))

def wra.proj(m: Maybe<&2, FWa.Req>, d: FWa.Req) -> FWa.Req:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def wra.end(e: Bool, +q2: FWa.Req, +q: FWa.Req, got: {SpW.r_whole.end(e, q2) == Some{q} : Maybe<&2, FWa.Req>}) -> {FWa.ffi.done(q2, e) == SpW.w_reply(q) : String}:
  match e:
    case True{}:
      +eq = Equal.cong(Maybe<&2, FWa.Req>, FWa.Req, m => wra.proj(m, q2), Some{q2}, Some{q}, got)
      %Equal.sym(FWa.Req, q2, q, eq) : {FWa.answer(_) == SpW.w_reply(q) : String}
      PWaitAnyEntryAnswers.wa.answer(q)
    case False{}:
      wra.none_some(q, {FWa.ffi.done(q2, False{}) == SpW.w_reply(q) : String}, got)

def wra.got(r: Wr.Dec<FWa.Req>, +q: FWa.Req, got: {SpW.r_whole(r) == Some{q} : Maybe<&2, FWa.Req>}) -> {FWa.ffi.got(r) == SpW.w_reply(q) : String}:
  match r:
    case Wr.Got{+q2, +s}:
      wra.end(Wr.end(s), q2, q, got)
    case Wr.Bad{}:
      wra.none_some(q, {FWa.ffi.got(Wr.Bad{}) == SpW.w_reply(q) : String}, got)

def WaitAny.wait_any_entry_read_answers(s, q, got):
  %Equal.sym(Wr.Dec<FWa.Req>, FWa.get_req(s), SpW.r_req(s), LW.wa.req(s)) : {FWa.ffi.got(_) == SpW.w_reply(q) : String}
  wra.got(SpW.r_req(s), q, got)

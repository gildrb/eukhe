# eukhe: the proof of LAW tui_color_ffi_malformed_exact
# The entry reads every input as the laws' reader does (LA.tcf.req);
# where that reader finds no whole request, the entry answers its error
# form.

import Base
import ../../bend/ffi_tui_color.bend as FTC
import ../../bend/wire.bend as Wr
import ../../laws/tui_color.bend as TuiColor
import ./base.bend as LA

def tme.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def tme.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : tme.if_none(A, _, G)
  Unit{}

def tme.end(b: Bool, -q: FTC.Req, no: {TuiColor.read_req.end(b, q) == None{} : Maybe<&2, FTC.Req>}) -> {FTC.run.end(b, q) == TuiColor.malformed_err() : String}:
  match b:
    case True{}:
      tme.some_none(FTC.Req, q, {FTC.answer(q) == TuiColor.malformed_err() : String}, no)
    case False{}:
      {==}

def tme.whole(r: Wr.Dec<FTC.Req>, no: {TuiColor.read_req.whole(r) == None{} : Maybe<&2, FTC.Req>}) -> {FTC.run(r) == TuiColor.malformed_err() : String}:
  match r:
    case Wr.Got{q, s}:
      tme.end(Wr.end(s), q, no)
    case Wr.Bad{}:
      {==}

def TuiColor.tui_color_ffi_malformed_exact(s, no):
  %LA.tcf.req(Wr.get_nat(s)) : {FTC.run(_) == TuiColor.malformed_err() : String}
  tme.whole(TuiColor.read_req.go(Wr.get_nat(s)), no)

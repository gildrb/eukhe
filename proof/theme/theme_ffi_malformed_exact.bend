# eukhe: the proof of LAW theme_ffi_malformed_exact
# The entry reads every input as the laws' reader does (LTRead); where
# that reader finds no whole request, the entry answers its error form.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_theme.bend as FTh
import ../../spec/theme/read.bend as Tr
import ../../laws/theme.bend as Theme
import ./base/ffi_read.bend as LTRead

def tm.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def tm.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : tm.if_none(A, _, G)
  Unit{}

def tm.end(b: Bool, -r: FTh.Req, no: {Tr.read.req.end(b, r) == None{} : Maybe<&2, FTh.Req>}) -> {FTh.run.end(b, r) == Tr.refused() : String}:
  match b:
    case True{}:
      tm.some_none(FTh.Req, r, {FTh.reply(r) == Tr.refused() : String}, no)
    case False{}:
      {==}

def tm.whole(d: Wr.Dec<FTh.Req>, no: {Tr.read.req.whole(d) == None{} : Maybe<&2, FTh.Req>}) -> {FTh.run(d) == Tr.refused() : String}:
  match d:
    case Wr.Got{r, s}:
      tm.end(Wr.end(s), r, no)
    case Wr.Bad{}:
      {==}

def Theme.theme_ffi_malformed_exact(s, no):
  %LTRead.tl.req.go(Wr.get_nat(s)) : {FTh.run(_) == Tr.refused() : String}
  tm.whole(Tr.read.req.go(Wr.get_nat(s)), no)

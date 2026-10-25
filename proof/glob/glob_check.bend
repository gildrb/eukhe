# eukhe: the proof of LAW glob_check
#
# PROOF: the error query reads the parse; split on the parse's answer.

import Base
import ../../bend/glob/parse.bend as GParse
import ../../bend/glob/queries.bend as GQuery
import ../../laws/glob.bend as Glob

def gck.r(r: Result<&2, &2, GParse.Err, GParse.Glob>) -> {GQuery.check.r(r) == Glob.sp_check(r) : Maybe<&2, GParse.Err>}:
  match r:
    case Fail{e}:
      {==}
    case Done{g}:
      {==}

def Glob.glob_check(p):
  gck.r(GParse.parse(p))

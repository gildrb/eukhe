# eukhe: the proof of LAW runners_ffi_refuses
#
# PROOF: the entry answers either the model's decision, which opens with a count (never 'E': the rosters compute), or the one error form; so an answer that opens with 'E' is that error form.

import Base
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/runners.bend as Runners
import ../base/staging.bend as LStg

def rrf.answer(q: FRu.Req) -> {LawsBase.wire_opens_err(FRu.answer(q)) == False{} : Bool}:
  match q:
    case FRu.QRegistry{}:
      {==}
    case FRu.QMain{h}:
      match h:
        case True{}:
          {==}
        case False{}:
          {==}

def rrf.end(b: Bool, +q: FRu.Req, bad: {LawsBase.wire_opens_err(FRu.run.end(b, q)) == True{} : Bool}) -> {FRu.run.end(b, q) == Runners.malformed() : String}:
  match b:
    case True{}:
      LStg.stg.absurd({FRu.answer(q) == Runners.malformed() : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FRu.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FRu.answer(q)), True{}, bad), rrf.answer(q)))
    case False{}:
      {==}

def rrf.run(d: Wr.Dec<FRu.Req>, bad: {LawsBase.wire_opens_err(FRu.run(d)) == True{} : Bool}) -> {FRu.run(d) == Runners.malformed() : String}:
  match d:
    case Wr.Got{+q, +rest}:
      rrf.end(Wr.end(rest), q, bad)
    case Wr.Bad{}:
      {==}

def Runners.runners_ffi_refuses(s, bad):
  rrf.run(FRu.get_req(s), bad)

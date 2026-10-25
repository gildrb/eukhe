# eukhe: the proof of LAW slash_suggest_entry_refuses
#
# PROOF: the entry answers either a suggestion, Nats (never 'E':
# wire_nat_not_err), or the one error form; so an answer that opens with
# 'E' is that error form.

import Base
import ../../bend/slash_suggest.bend as Ss
import ../../bend/ffi_slash_suggest.bend as FSs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/slash_suggest.bend as SlashSuggest
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def ssf.put_ok(m: Maybe<&2, Nat>) -> {LawsBase.wire_opens_err(FSs.put_answer(m)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{j}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(j, ""))

def ssf.answer_ok(q: FSs.Req) -> {LawsBase.wire_opens_err(FSs.answer(q)) == False{} : Bool}:
  match q:
    case FSs.QSuggest{w, cs}:
      ssf.put_ok(Ss.suggest(w, cs))

def ssf.refuse(d: Wr.Dec<FSs.Req>, bad: {LawsBase.wire_opens_err(FSs.ffi.got(d)) == True{} : Bool}) -> {FSs.ffi.got(d) == Wr.err("slash_suggest: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FSs.answer(q) == Wr.err("slash_suggest: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FSs.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FSs.answer(q)), True{}, bad), ssf.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def SlashSuggest.slash_suggest_entry_refuses(s, bad):
  ssf.refuse(FSs.get_req(s), bad)

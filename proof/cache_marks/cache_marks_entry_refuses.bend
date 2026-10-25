# eukhe: the proof of LAW cache_marks_entry_refuses
#
# PROOF: the entry answers either a decision, which opens with a count or
# a Nat (never 'E': wire_nat_not_err), or the one error form; so an answer
# that opens with 'E' is that error form.

import Base
import ../../bend/cache_marks.bend as Cm
import ../../bend/ffi_cache_marks.bend as FCm
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/cache_marks.bend as CacheMarks
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg
import ../base/wire_dec.bend as LE

def cmf.put_ok(m: Maybe<&2, String>) -> {LawsBase.wire_opens_err(FCm.put_excess(m)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      Wire.wire_nat_not_err(1n, Wr.put_str(e, ""))

def cmf.answer_ok(q: FCm.Req) -> {LawsBase.wire_opens_err(FCm.answer(q)) == False{} : Bool}:
  match q:
    case FCm.QExcess{n}:
      cmf.put_ok(Cm.excess(n))
    case FCm.QGrant{p, ws}:
      LE.dcw.fin_ok(Wr.put_list.go(~Bool, ~Wr.put_bool, Cm.grant(p, ws), ""))

def cmf.refuse(d: Wr.Dec<FCm.Req>, bad: {LawsBase.wire_opens_err(FCm.ffi.got(d)) == True{} : Bool}) -> {FCm.ffi.got(d) == Wr.err("cache_marks: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FCm.answer(q) == Wr.err("cache_marks: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FCm.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FCm.answer(q)), True{}, bad), cmf.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def CacheMarks.cache_marks_entry_refuses(s, bad):
  cmf.refuse(FCm.get_req(s), bad)

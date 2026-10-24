# eukhe: the proof of LAW commit_entry_refuses
#
# PROOF: the entry answers either a request's choice or the one error
# form; every choice opens with a tag, a count or a length, never 'E'
# (wire_nat_not_err); so an answer that opens with 'E' is the error form.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../bend/ffi_doc_commit.bend as FCm
import ../../bend/wire.bend as Wr
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./base.bend as LA
import ./entry/wire.bend as LE

def dcw.ok_check(c: Cm.Check) -> {LawsBase.wire_opens_err(FCm.put_check(c)) == False{} : Bool}:
  match c:
    case Cm.Go{}:
      {==}
    case Cm.Stop{at, why}:
      match why:
        case Cm.Changed{}:
          {==}
        case Cm.Taken{}:
          {==}

def dcw.ok_outcome(o: Cm.Outcome) -> {LawsBase.wire_opens_err(FCm.put_outcome(o)) == False{} : Bool}:
  match o:
    case Cm.Lands{w}:
      {==}
    case Cm.Fails{}:
      {==}

def dcw.ok_verdict(v: Cm.Verdict) -> {LawsBase.wire_opens_err(FCm.put_verdict(v)) == False{} : Bool}:
  match v:
    case Cm.Failure{}:
      {==}
    case Cm.Summary{ns, p}:
      {==}

# a request's choice is a value, never the error form
def dcw.answer_ok(q: FCm.Req) -> {LawsBase.wire_opens_err(FCm.answer(q)) == False{} : Bool}:
  match q:
    case FCm.QCheck{ms}:
      dcw.ok_check(Cm.check(ms))
    case FCm.QPublish{p}:
      dcw.ok_outcome(Cm.outcome(p))
    case FCm.QAnswer{fs}:
      dcw.ok_verdict(Cm.answer(fs))
    case FCm.QGate{b, d}:
      Wire.wire_nat_not_err(FCm.gate.tag(Cm.gate(b, d)), "")
    case FCm.QSeen{d, xs}:
      LE.dcw.fin_ok(Wr.put_list.go(~String, ~Wr.put_str, Cm.seen(d, xs), ""))
    case FCm.QPrefix{h}:
      LE.dcw.sfin_ok(Wr.put_str.go(Cm.prefix(h), SNil{}, 0n), "")
    case FCm.QSweep{h, es}:
      LE.dcw.fin_ok(Wr.put_list.go(~Nat, ~Wr.put_nat, Cm.gone(h, es), ""))

def dcw.refuse(d: Wr.Dec<FCm.Req>, bad: {LawsBase.wire_opens_err(FCm.ffi.got(d)) == True{} : Bool}) -> {FCm.ffi.got(d) == Wr.err("doc_commit: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LA.dcw.tf({FCm.answer(q) == Wr.err("doc_commit: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FCm.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FCm.answer(q)), True{}, bad), dcw.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def DocCommit.commit_entry_refuses(s, bad):
  dcw.refuse(FCm.get_req(s), bad)

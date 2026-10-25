# eukhe: the proof of LAW stream_failure_entry_refuses
#
# PROOF: every answer opens with a count, a tag or a string length (never 'E':
# wire_nat_not_err), or is the one error form; so an answer that opens
# with 'E' is that error form.

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/stream_failure.bend as Sf
import ../../bend/ffi_stream_failure.bend as FSf
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as OverflowLaws
import ../../laws/stream_failure.bend as StreamFailure
import ./base.bend as LA
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg
import ../base/wire_dec.bend as LE

def sff.cause(k: Sf.Cause, rest: String) -> {LawsBase.wire_opens_err(FSf.put_cause(k, rest)) == False{} : Bool}:
  match k:
    case Sf.KRefusal{}:
      Wire.wire_nat_not_err(0n, rest)
    case Sf.KSafety{}:
      Wire.wire_nat_not_err(1n, rest)
    case Sf.KPayment{}:
      Wire.wire_nat_not_err(2n, rest)
    case Sf.KOverloaded{}:
      Wire.wire_nat_not_err(3n, rest)
    case Sf.KRateLimit{}:
      Wire.wire_nat_not_err(4n, rest)
    case Sf.KServer{}:
      Wire.wire_nat_not_err(5n, rest)
    case Sf.KAuth{}:
      Wire.wire_nat_not_err(6n, rest)
    case Sf.KPermission{}:
      Wire.wire_nat_not_err(7n, rest)
    case Sf.KInvalid{}:
      Wire.wire_nat_not_err(8n, rest)
    case Sf.KMalformed{}:
      Wire.wire_nat_not_err(9n, rest)
    case Sf.KDrop{}:
      Wire.wire_nat_not_err(10n, rest)
    case Sf.KStalled{}:
      Wire.wire_nat_not_err(11n, rest)
    case Sf.KRepeating{}:
      Wire.wire_nat_not_err(12n, rest)
    case Sf.KUnknown{}:
      Wire.wire_nat_not_err(13n, rest)

def sff.str(x: String, rest: String) -> {LawsBase.wire_opens_err(Wr.put_str(x, rest)) == False{} : Bool}:
  LE.dcw.sfin_ok(Wr.put_str.go(x, "", 0n), rest)

def sff.http(h: Sf.Http) -> {LawsBase.wire_opens_err(FSf.put_http(h)) == False{} : Bool}:
  match h:
    case Sf.Http{k, t, m}:
      sff.cause(k, FSf.put_mstr(t, FSf.put_mstr(m, "")))

def sff.named(n: Sf.Named) -> {LawsBase.wire_opens_err(FSf.put_named(n)) == False{} : Bool}:
  match n:
    case Sf.Named{k, m}:
      sff.cause(k, Wr.put_str(m, ""))

def sff.repeat(x: Sf.Repeat) -> {LawsBase.wire_opens_err(FSf.put_repeat(x)) == False{} : Bool}:
  match x:
    case Sf.Repeat{m, p}:
      sff.str(m, Wr.put_nat(p, ""))

def sff.answer_ok(q: FSf.Req) -> {LawsBase.wire_opens_err(FSf.answer(q)) == False{} : Bool}:
  match q:
    case FSf.QClassify{t, st}:
      sff.cause(Sf.classify(t, st), "")
    case FSf.QMessage{k, t, st, d, r}:
      sff.str(Sf.message(k, t, st, d, r), "")
    case FSf.QHttp{m, st, bt, d, code, sdk, r}:
      sff.http(Sf.http(m, st, bt, d, code, sdk, r))
    case FSf.QFromStop{raw, r}:
      sff.named(Sf.from_stop(raw, r))
    case FSf.QDrop{b}:
      sff.str(Sf.drop(b), "")
    case FSf.QStalled{ms}:
      sff.str(Sf.stalled(ms), "")
    case FSf.QShown{line}:
      sff.str(Sf.shown(line), "")
    case FSf.QRepeating{limit, period, q}:
      sff.repeat(Sf.repeating(limit, period, q))

def sff.refuse(d: Wr.Dec<FSf.Req>, bad: {LawsBase.wire_opens_err(FSf.ffi.got(d)) == True{} : Bool}) -> {FSf.ffi.got(d) == Wr.err("stream_failure: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FSf.answer(q) == Wr.err("stream_failure: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FSf.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FSf.answer(q)), True{}, bad), sff.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def StreamFailure.stream_failure_entry_refuses(s, bad):
  sff.refuse(FSf.get_req(s), bad)

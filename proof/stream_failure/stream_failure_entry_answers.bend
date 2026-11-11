# eukhe: the proof of LAW stream_failure_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (stream_failure_entry_reads), so the entry answers the code's decision,
# encoded as the laws spell it (sfa.*).

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
import ./stream_failure_entry_reads.bend as PStreamFailureEntryReads

def sfa.cause(k: Sf.Cause, rest: String) -> {FSf.put_cause(k, rest) == StreamFailure.sp_w_cause(k, rest) : String}:
  match k:
    case Sf.KRefusal{}:
      {==}
    case Sf.KSafety{}:
      {==}
    case Sf.KPayment{}:
      {==}
    case Sf.KOverloaded{}:
      {==}
    case Sf.KRateLimit{}:
      {==}
    case Sf.KServer{}:
      {==}
    case Sf.KAuth{}:
      {==}
    case Sf.KPermission{}:
      {==}
    case Sf.KInvalid{}:
      {==}
    case Sf.KMalformed{}:
      {==}
    case Sf.KDrop{}:
      {==}
    case Sf.KStalled{}:
      {==}
    case Sf.KRepeating{}:
      {==}
    case Sf.KUnknown{}:
      {==}

def sfa.mstr(m: Maybe<&2, String>, rest: String) -> {FSf.put_mstr(m, rest) == StreamFailure.sp_w_mstr(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def sfa.http(h: Sf.Http) -> {FSf.put_http(h) == StreamFailure.sp_w_http(h) : String}:
  match h:
    case Sf.Http{+k, +t, +m}:
      %Equal.sym(String, FSf.put_mstr(m, ""), StreamFailure.sp_w_mstr(m, ""), sfa.mstr(m, "")) : {FSf.put_cause(k, FSf.put_mstr(t, _)) == StreamFailure.sp_w_http(Sf.Http{k, t, m}) : String}
      %Equal.sym(String, FSf.put_mstr(t, StreamFailure.sp_w_mstr(m, "")), StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mstr(m, "")), sfa.mstr(t, StreamFailure.sp_w_mstr(m, ""))) : {FSf.put_cause(k, _) == StreamFailure.sp_w_http(Sf.Http{k, t, m}) : String}
      sfa.cause(k, StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mstr(m, "")))

def sfa.named(n: Sf.Named) -> {FSf.put_named(n) == StreamFailure.sp_w_named(n) : String}:
  match n:
    case Sf.Named{+k, +m}:
      sfa.cause(k, Wr.put_str(m, ""))

def sfa.repeat(x: Sf.Repeat) -> {FSf.put_repeat(x) == StreamFailure.sp_w_repeat(x) : String}:
  match x:
    case Sf.Repeat{m, p}:
      {==}

def sfa.reply(q: FSf.Req) -> {FSf.answer(q) == StreamFailure.sp_w_reply(q) : String}:
  match q:
    case FSf.QClassify{+t, +st}:
      sfa.cause(Sf.classify(t, st), "")
    case FSf.QMessage{k, t, st, d, r}:
      {==}
    case FSf.QHttp{+m, +st, +bt, +d, +code, +sdk, +r}:
      sfa.http(Sf.http(m, st, bt, d, code, sdk, r))
    case FSf.QFromStop{+raw, +r}:
      sfa.named(Sf.from_stop(raw, r))
    case FSf.QDrop{b}:
      {==}
    case FSf.QStalled{ms}:
      {==}
    case FSf.QShown{line}:
      {==}
    case FSf.QRepeating{+limit, +period, +q}:
      sfa.repeat(Sf.repeating(limit, period, q))

def StreamFailure.stream_failure_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FSf.Req>, FSf.get_req(StreamFailure.sp_w_req(q, "")), Wr.Got{q, ""}, StreamFailure.stream_failure_entry_reads(q, "", h)) : {FSf.ffi.got(_) == StreamFailure.sp_w_reply(q) : String}
  sfa.reply(q)

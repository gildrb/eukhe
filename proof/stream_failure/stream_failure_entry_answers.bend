# eukhe: the proof of LAW stream_failure_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (stream_failure_entry_reads), so the entry answers the code's decision,
# which is the spec's (the decision lemmas of LA.sfb), encoded as the spec
# spells it (sfa.*).

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
      %Equal.sym(Sf.Cause, Sf.classify(t, st), StreamFailure.sp_classify(t, st), LA.sfb.classify(t, st)) : {FSf.put_cause(_, "") == StreamFailure.sp_w_cause(StreamFailure.sp_classify(t, st), "") : String}
      sfa.cause(StreamFailure.sp_classify(t, st), "")
    case FSf.QMessage{+k, +t, +st, +d, +r}:
      %Equal.sym(String, Sf.message(k, t, st, d, r), StreamFailure.sp_message(k, t, st, d, r), LA.sfb.message(k, t, st, d, r)) : {Wr.put_str(_, "") == Wr.put_str(StreamFailure.sp_message(k, t, st, d, r), "") : String}
      {==}
    case FSf.QHttp{+m, +st, +bt, +d, +code, +sdk, +r}:
      %Equal.sym(Sf.Http, Sf.http(m, st, bt, d, code, sdk, r), StreamFailure.sp_http(m, st, bt, d, code, sdk, r), LA.sfb.http(m, st, bt, d, code, sdk, r)) : {FSf.put_http(_) == StreamFailure.sp_w_http(StreamFailure.sp_http(m, st, bt, d, code, sdk, r)) : String}
      sfa.http(StreamFailure.sp_http(m, st, bt, d, code, sdk, r))
    case FSf.QFromStop{+raw, +r}:
      %Equal.sym(Sf.Named, Sf.from_stop(raw, r), StreamFailure.sp_from_stop(raw, r), LA.sfb.from_stop(raw, r)) : {FSf.put_named(_) == StreamFailure.sp_w_named(StreamFailure.sp_from_stop(raw, r)) : String}
      sfa.named(StreamFailure.sp_from_stop(raw, r))
    case FSf.QDrop{+b}:
      %Equal.sym(String, Sf.drop.detail(b), StreamFailure.sp_drop_detail(b), LA.sfb.drop_detail(b)) : {Wr.put_str(Sf.message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{_}, None{}), "") == StreamFailure.sp_w_reply(FSf.QDrop{b}) : String}
      %Equal.sym(String, Sf.message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{StreamFailure.sp_drop_detail(b)}, None{}), StreamFailure.sp_message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{StreamFailure.sp_drop_detail(b)}, None{}), LA.sfb.message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{StreamFailure.sp_drop_detail(b)}, None{})) : {Wr.put_str(_, "") == StreamFailure.sp_w_reply(FSf.QDrop{b}) : String}
      {==}
    case FSf.QStalled{+ms}:
      %Equal.sym(String, Sf.message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{}), StreamFailure.sp_message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{}), LA.sfb.message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{})) : {Wr.put_str(_, "") == StreamFailure.sp_w_reply(FSf.QStalled{ms}) : String}
      {==}
    case FSf.QShown{+line}:
      %Equal.sym(String, Sf.shown(line), StreamFailure.sp_shown(line), LA.sfb.shown(line)) : {Wr.put_str(_, "") == Wr.put_str(StreamFailure.sp_shown(line), "") : String}
      {==}
    case FSf.QRepeating{+limit, +period, +q}:
      %Equal.sym(Sf.Repeat, Sf.repeating(limit, period, q), StreamFailure.sp_repeating(limit, period, q), LA.sfb.repeating(limit, period, q)) : {FSf.put_repeat(_) == StreamFailure.sp_w_repeat(StreamFailure.sp_repeating(limit, period, q)) : String}
      sfa.repeat(StreamFailure.sp_repeating(limit, period, q))

def StreamFailure.stream_failure_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FSf.Req>, FSf.get_req(StreamFailure.sp_w_req(q, "")), Wr.Got{q, ""}, StreamFailure.stream_failure_entry_reads(q, "", h)) : {FSf.ffi.got(_) == StreamFailure.sp_w_reply(q) : String}
  sfa.reply(q)

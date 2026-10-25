# eukhe: the proof of LAW stream_failure_entry_reads
#
# PROOF: the question's tag reads back, then each field by its round trip
# (sfr.*: a Maybe, a cause, a block; the wire laws for numbers and texts;
# every number and length fits by the premise), so each stage of the
# decoder hands the next one exactly the rest after its field.

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
import ../base/logic/bool.bend as LLogicBool

def sfr.mstr(m: Maybe<&2, String>, +rest: String, f: {StreamFailure.sp_fit_mstr(m) == True{} : Bool}) -> {FSf.get_mstr(StreamFailure.sp_w_mstr(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, f)) : {FSf.get_mstr.of(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}

def sfr.mnat(m: Maybe<&2, Nat>, +rest: String, f: {StreamFailure.sp_fit_mnat(m) == True{} : Bool}) -> {FSf.get_mnat(StreamFailure.sp_w_mnat(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(x, rest)), Wr.Got{x, rest}, Wire.wire_nat_round_trip(x, rest, f)) : {FSf.get_mnat.of(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def sfr.cause(k: Sf.Cause, rest: String) -> {FSf.get_cause(StreamFailure.sp_w_cause(k, rest)) == Wr.Got{k, rest} : Wr.Dec<Sf.Cause>}:
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

def sfr.block(b: Sf.Block, rest: String) -> {FSf.get_block(StreamFailure.sp_w_block(b, rest)) == Wr.Got{b, rest} : Wr.Dec<Sf.Block>}:
  match b:
    case Sf.BThinking{}:
      {==}
    case Sf.BText{}:
      {==}
    case Sf.BToolCall{}:
      {==}
    case Sf.BNone{}:
      {==}

def sfr.req(q: FSf.Req, +rest: String, h: {StreamFailure.sp_fit_req(q) == True{} : Bool}) -> {FSf.get_req(StreamFailure.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FSf.Req>}:
  match q:
    case FSf.QClassify{+t, +st}:
      +h0 = h
      +ft = LLogicBool.tree.pt.and_l(StreamFailure.sp_fit_mstr(t), StreamFailure.sp_fit_mnat(st), h0)
      +h1 = LLogicBool.tree.pt.and_r(StreamFailure.sp_fit_mstr(t), StreamFailure.sp_fit_mnat(st), h0)
      +fst = h1
      +r1 = StreamFailure.sp_w_mnat(st, rest)
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSf.get_mstr(StreamFailure.sp_w_mstr(t, r1)), Wr.Got{t, r1}, sfr.mstr(t, r1, ft)) : {FSf.get_classify.t(_) == Wr.Got{FSf.QClassify{t, st}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, FSf.get_mnat(StreamFailure.sp_w_mnat(st, rest)), Wr.Got{st, rest}, sfr.mnat(st, rest, fst)) : {FSf.get_classify.st(t, _) == Wr.Got{FSf.QClassify{t, st}, rest} : Wr.Dec<FSf.Req>}
      {==}
    case FSf.QMessage{+k, +t, +st, +d, +r}:
      +h0 = h
      +ft = LLogicBool.tree.pt.and_l(StreamFailure.sp_fit_mstr(t), Bool.and(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(d), StreamFailure.sp_fit_mstr(r))), h0)
      +h1 = LLogicBool.tree.pt.and_r(StreamFailure.sp_fit_mstr(t), Bool.and(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(d), StreamFailure.sp_fit_mstr(r))), h0)
      +fst = LLogicBool.tree.pt.and_l(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(d), StreamFailure.sp_fit_mstr(r)), h1)
      +h2 = LLogicBool.tree.pt.and_r(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(d), StreamFailure.sp_fit_mstr(r)), h1)
      +fd = LLogicBool.tree.pt.and_l(StreamFailure.sp_fit_mstr(d), StreamFailure.sp_fit_mstr(r), h2)
      +h3 = LLogicBool.tree.pt.and_r(StreamFailure.sp_fit_mstr(d), StreamFailure.sp_fit_mstr(r), h2)
      +fr = h3
      +r1 = StreamFailure.sp_w_mstr(t, StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(r, rest))))
      +r2 = StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(r, rest)))
      +r3 = StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(r, rest))
      +r4 = StreamFailure.sp_w_mstr(r, rest)
      %Equal.sym(Wr.Dec<Sf.Cause>, FSf.get_cause(StreamFailure.sp_w_cause(k, r1)), Wr.Got{k, r1}, sfr.cause(k, r1)) : {FSf.get_message.k(_) == Wr.Got{FSf.QMessage{k, t, st, d, r}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSf.get_mstr(StreamFailure.sp_w_mstr(t, r2)), Wr.Got{t, r2}, sfr.mstr(t, r2, ft)) : {FSf.get_message.t(k, _) == Wr.Got{FSf.QMessage{k, t, st, d, r}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, FSf.get_mnat(StreamFailure.sp_w_mnat(st, r3)), Wr.Got{st, r3}, sfr.mnat(st, r3, fst)) : {FSf.get_message.st(k, t, _) == Wr.Got{FSf.QMessage{k, t, st, d, r}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSf.get_mstr(StreamFailure.sp_w_mstr(d, r4)), Wr.Got{d, r4}, sfr.mstr(d, r4, fd)) : {FSf.get_message.d(k, t, st, _) == Wr.Got{FSf.QMessage{k, t, st, d, r}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSf.get_mstr(StreamFailure.sp_w_mstr(r, rest)), Wr.Got{r, rest}, sfr.mstr(r, rest, fr)) : {FSf.get_message.r(k, t, st, d, _) == Wr.Got{FSf.QMessage{k, t, st, d, r}, rest} : Wr.Dec<FSf.Req>}
      {==}
    case FSf.QHttp{+m, +st, +bt, +d, +code, +sdk, +r}:
      +h0 = h
      +fm = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(m)), Bool.and(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(bt), Bool.and(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r)))))), h0)
      +h1 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(m)), Bool.and(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(bt), Bool.and(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r)))))), h0)
      +fst = LLogicBool.tree.pt.and_l(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(bt), Bool.and(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r))))), h1)
      +h2 = LLogicBool.tree.pt.and_r(StreamFailure.sp_fit_mnat(st), Bool.and(StreamFailure.sp_fit_mstr(bt), Bool.and(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r))))), h1)
      +fbt = LLogicBool.tree.pt.and_l(StreamFailure.sp_fit_mstr(bt), Bool.and(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r)))), h2)
      +h3 = LLogicBool.tree.pt.and_r(StreamFailure.sp_fit_mstr(bt), Bool.and(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r)))), h2)
      +fd = LLogicBool.tree.pt.and_l(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r))), h3)
      +h4 = LLogicBool.tree.pt.and_r(StreamFailure.sp_fit_mstr(d), Bool.and(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r))), h3)
      +fcode = LLogicBool.tree.pt.and_l(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r)), h4)
      +h5 = LLogicBool.tree.pt.and_r(StreamFailure.sp_fit_mstr(code), Bool.and(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r)), h4)
      +fsdk = LLogicBool.tree.pt.and_l(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r), h5)
      +h6 = LLogicBool.tree.pt.and_r(StreamFailure.sp_fit_mstr(sdk), StreamFailure.sp_fit_mstr(r), h5)
      +fr = h6
      +r1 = StreamFailure.sp_w_mnat(st, StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, StreamFailure.sp_w_mstr(sdk, StreamFailure.sp_w_mstr(r, rest))))))
      +r2 = StreamFailure.sp_w_mstr(bt, StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, StreamFailure.sp_w_mstr(sdk, StreamFailure.sp_w_mstr(r, rest)))))
      +r3 = StreamFailure.sp_w_mstr(d, StreamFailure.sp_w_mstr(code, StreamFailure.sp_w_mstr(sdk, StreamFailure.sp_w_mstr(r, rest))))
      +r4 = StreamFailure.sp_w_mstr(code, StreamFailure.sp_w_mstr(sdk, StreamFailure.sp_w_mstr(r, rest)))
      +r5 = StreamFailure.sp_w_mstr(sdk, StreamFailure.sp_w_mstr(r, rest))
      +r6 = StreamFailure.sp_w_mstr(r, rest)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(m, r1)), Wr.Got{m, r1}, Wire.wire_str_round_trip(m, r1, fm)) : {FSf.get_http.m(_) == Wr.Got{FSf.QHttp{m, st, bt, d, code, sdk, r}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, FSf.get_mnat(StreamFailure.sp_w_mnat(st, r2)), Wr.Got{st, r2}, sfr.mnat(st, r2, fst)) : {FSf.get_http.st(m, _) == Wr.Got{FSf.QHttp{m, st, bt, d, code, sdk, r}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSf.get_mstr(StreamFailure.sp_w_mstr(bt, r3)), Wr.Got{bt, r3}, sfr.mstr(bt, r3, fbt)) : {FSf.get_http.bt(m, st, _) == Wr.Got{FSf.QHttp{m, st, bt, d, code, sdk, r}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSf.get_mstr(StreamFailure.sp_w_mstr(d, r4)), Wr.Got{d, r4}, sfr.mstr(d, r4, fd)) : {FSf.get_http.d(m, st, bt, _) == Wr.Got{FSf.QHttp{m, st, bt, d, code, sdk, r}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSf.get_mstr(StreamFailure.sp_w_mstr(code, r5)), Wr.Got{code, r5}, sfr.mstr(code, r5, fcode)) : {FSf.get_http.code(m, st, bt, d, _) == Wr.Got{FSf.QHttp{m, st, bt, d, code, sdk, r}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSf.get_mstr(StreamFailure.sp_w_mstr(sdk, r6)), Wr.Got{sdk, r6}, sfr.mstr(sdk, r6, fsdk)) : {FSf.get_http.sdk(m, st, bt, d, code, _) == Wr.Got{FSf.QHttp{m, st, bt, d, code, sdk, r}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSf.get_mstr(StreamFailure.sp_w_mstr(r, rest)), Wr.Got{r, rest}, sfr.mstr(r, rest, fr)) : {FSf.get_http.r(m, st, bt, d, code, sdk, _) == Wr.Got{FSf.QHttp{m, st, bt, d, code, sdk, r}, rest} : Wr.Dec<FSf.Req>}
      {==}
    case FSf.QFromStop{+raw, +r}:
      +h0 = h
      +fraw = LLogicBool.tree.pt.and_l(StreamFailure.sp_fit_mstr(raw), StreamFailure.sp_fit_mstr(r), h0)
      +h1 = LLogicBool.tree.pt.and_r(StreamFailure.sp_fit_mstr(raw), StreamFailure.sp_fit_mstr(r), h0)
      +fr = h1
      +r1 = StreamFailure.sp_w_mstr(r, rest)
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSf.get_mstr(StreamFailure.sp_w_mstr(raw, r1)), Wr.Got{raw, r1}, sfr.mstr(raw, r1, fraw)) : {FSf.get_fromstop.raw(_) == Wr.Got{FSf.QFromStop{raw, r}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSf.get_mstr(StreamFailure.sp_w_mstr(r, rest)), Wr.Got{r, rest}, sfr.mstr(r, rest, fr)) : {FSf.get_fromstop.r(raw, _) == Wr.Got{FSf.QFromStop{raw, r}, rest} : Wr.Dec<FSf.Req>}
      {==}
    case FSf.QDrop{+b}:
      %Equal.sym(Wr.Dec<Sf.Block>, FSf.get_block(StreamFailure.sp_w_block(b, rest)), Wr.Got{b, rest}, sfr.block(b, rest)) : {FSf.get_drop.b(_) == Wr.Got{FSf.QDrop{b}, rest} : Wr.Dec<FSf.Req>}
      {==}
    case FSf.QStalled{+ms}:
      +h0 = h
      +fms = h0
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(ms, rest)), Wr.Got{ms, rest}, Wire.wire_str_round_trip(ms, rest, fms)) : {FSf.get_stalled.ms(_) == Wr.Got{FSf.QStalled{ms}, rest} : Wr.Dec<FSf.Req>}
      {==}
    case FSf.QShown{+line}:
      +h0 = h
      +fline = h0
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(line, rest)), Wr.Got{line, rest}, Wire.wire_str_round_trip(line, rest, fline)) : {FSf.get_shown.line(_) == Wr.Got{FSf.QShown{line}, rest} : Wr.Dec<FSf.Req>}
      {==}
    case FSf.QRepeating{+limit, +period, +q}:
      +h0 = h
      +flimit = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(limit), Bool.and(LawsBase.wire_fits(period), LawsBase.wire_fits(String.length(q))), h0)
      +h1 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(limit), Bool.and(LawsBase.wire_fits(period), LawsBase.wire_fits(String.length(q))), h0)
      +fperiod = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(period), LawsBase.wire_fits(String.length(q)), h1)
      +h2 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(period), LawsBase.wire_fits(String.length(q)), h1)
      +fq = h2
      +r1 = Wr.put_nat(period, Wr.put_str(q, rest))
      +r2 = Wr.put_str(q, rest)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(limit, r1)), Wr.Got{limit, r1}, Wire.wire_nat_round_trip(limit, r1, flimit)) : {FSf.get_repeating.limit(_) == Wr.Got{FSf.QRepeating{limit, period, q}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(period, r2)), Wr.Got{period, r2}, Wire.wire_nat_round_trip(period, r2, fperiod)) : {FSf.get_repeating.period(limit, _) == Wr.Got{FSf.QRepeating{limit, period, q}, rest} : Wr.Dec<FSf.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(q, rest)), Wr.Got{q, rest}, Wire.wire_str_round_trip(q, rest, fq)) : {FSf.get_repeating.q(limit, period, _) == Wr.Got{FSf.QRepeating{limit, period, q}, rest} : Wr.Dec<FSf.Req>}
      {==}

def StreamFailure.stream_failure_entry_reads(q, rest, h):
  sfr.req(q, rest, h)

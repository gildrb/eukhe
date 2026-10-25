# eukhe: the proof of LAW error_body_entry_reads
#
# PROOF: the question's tag reads back, then each field by its round trip
# (ebr.probe, ebr.mstr; the wire laws for texts, Bools and Nats; every
# number and length fits by the premise), so each stage of the decoder
# hands the next one exactly the rest after its field.

import Base
import ../../bend/error_body.bend as Eb
import ../../bend/ffi_error_body.bend as FEb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/error_body.bend as ErrorBody
import ../base/logic/bool.bend as LLogicBool

def ebr.probe(p: Eb.Probe, +rest: String, f: {ErrorBody.sp_fit_probe(p) == True{} : Bool}) -> {FEb.get_probe(ErrorBody.sp_w_probe(p, rest)) == Wr.Got{p, rest} : Wr.Dec<Eb.Probe>}:
  match p:
    case Eb.PNone{}:
      {==}
    case Eb.PText{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, f)) : {FEb.get_probe.text(_) == Wr.Got{Eb.PText{x}, rest} : Wr.Dec<Eb.Probe>}
      {==}
    case Eb.PObj{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, f)) : {FEb.get_probe.obj(_) == Wr.Got{Eb.PObj{x}, rest} : Wr.Dec<Eb.Probe>}
      {==}

def ebr.mstr(m: Maybe<&2, String>, +rest: String, f: {ErrorBody.sp_fit_mstr(m) == True{} : Bool}) -> {FEb.get_mstr(ErrorBody.sp_w_mstr(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, f)) : {FEb.get_mstr.of(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}

def ebr.req(q: FEb.Req, +rest: String, h: {ErrorBody.sp_fit_req(q) == True{} : Bool}) -> {FEb.get_req(ErrorBody.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FEb.Req>}:
  match q:
    case FEb.QBody{+b, +e, +r}:
      +h0 = h
      +fb = LLogicBool.tree.pt.and_l(ErrorBody.sp_fit_probe(b), Bool.and(ErrorBody.sp_fit_probe(e), ErrorBody.sp_fit_probe(r)), h0)
      +h1 = LLogicBool.tree.pt.and_r(ErrorBody.sp_fit_probe(b), Bool.and(ErrorBody.sp_fit_probe(e), ErrorBody.sp_fit_probe(r)), h0)
      +fe = LLogicBool.tree.pt.and_l(ErrorBody.sp_fit_probe(e), ErrorBody.sp_fit_probe(r), h1)
      +fr = LLogicBool.tree.pt.and_r(ErrorBody.sp_fit_probe(e), ErrorBody.sp_fit_probe(r), h1)
      +r2 = ErrorBody.sp_w_probe(e, ErrorBody.sp_w_probe(r, rest))
      +r3 = ErrorBody.sp_w_probe(r, rest)
      %Equal.sym(Wr.Dec<Eb.Probe>, FEb.get_probe(ErrorBody.sp_w_probe(b, r2)), Wr.Got{b, r2}, ebr.probe(b, r2, fb)) : {FEb.get_body(_) == Wr.Got{FEb.QBody{b, e, r}, rest} : Wr.Dec<FEb.Req>}
      %Equal.sym(Wr.Dec<Eb.Probe>, FEb.get_probe(ErrorBody.sp_w_probe(e, r3)), Wr.Got{e, r3}, ebr.probe(e, r3, fe)) : {FEb.get_body.e(b, _) == Wr.Got{FEb.QBody{b, e, r}, rest} : Wr.Dec<FEb.Req>}
      %Equal.sym(Wr.Dec<Eb.Probe>, FEb.get_probe(ErrorBody.sp_w_probe(r, rest)), Wr.Got{r, rest}, ebr.probe(r, rest, fr)) : {FEb.get_body.r(b, e, _) == Wr.Got{FEb.QBody{b, e, r}, rest} : Wr.Dec<FEb.Req>}
      {==}
    case FEb.QShow{+c, +st, +b, +p, +m}:
      +h0 = h
      +fst = LLogicBool.tree.pt.and_l(ErrorBody.sp_fit_mstr(st), Bool.and(ErrorBody.sp_fit_mstr(b), Bool.and(ErrorBody.sp_fit_mstr(p), LawsBase.wire_fits(String.length(m)))), h0)
      +h1 = LLogicBool.tree.pt.and_r(ErrorBody.sp_fit_mstr(st), Bool.and(ErrorBody.sp_fit_mstr(b), Bool.and(ErrorBody.sp_fit_mstr(p), LawsBase.wire_fits(String.length(m)))), h0)
      +fb = LLogicBool.tree.pt.and_l(ErrorBody.sp_fit_mstr(b), Bool.and(ErrorBody.sp_fit_mstr(p), LawsBase.wire_fits(String.length(m))), h1)
      +h2 = LLogicBool.tree.pt.and_r(ErrorBody.sp_fit_mstr(b), Bool.and(ErrorBody.sp_fit_mstr(p), LawsBase.wire_fits(String.length(m))), h1)
      +fp = LLogicBool.tree.pt.and_l(ErrorBody.sp_fit_mstr(p), LawsBase.wire_fits(String.length(m)), h2)
      +fm = LLogicBool.tree.pt.and_r(ErrorBody.sp_fit_mstr(p), LawsBase.wire_fits(String.length(m)), h2)
      +r1 = ErrorBody.sp_w_mstr(st, ErrorBody.sp_w_mstr(b, ErrorBody.sp_w_mstr(p, Wr.put_str(m, rest))))
      +r2 = ErrorBody.sp_w_mstr(b, ErrorBody.sp_w_mstr(p, Wr.put_str(m, rest)))
      +r3 = ErrorBody.sp_w_mstr(p, Wr.put_str(m, rest))
      +r4 = Wr.put_str(m, rest)
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(c, r1)), Wr.Got{c, r1}, Wire.wire_bool_round_trip(c, r1)) : {FEb.get_show(_) == Wr.Got{FEb.QShow{c, st, b, p, m}, rest} : Wr.Dec<FEb.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FEb.get_mstr(ErrorBody.sp_w_mstr(st, r2)), Wr.Got{st, r2}, ebr.mstr(st, r2, fst)) : {FEb.get_show.st(c, _) == Wr.Got{FEb.QShow{c, st, b, p, m}, rest} : Wr.Dec<FEb.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FEb.get_mstr(ErrorBody.sp_w_mstr(b, r3)), Wr.Got{b, r3}, ebr.mstr(b, r3, fb)) : {FEb.get_show.b(c, st, _) == Wr.Got{FEb.QShow{c, st, b, p, m}, rest} : Wr.Dec<FEb.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FEb.get_mstr(ErrorBody.sp_w_mstr(p, r4)), Wr.Got{p, r4}, ebr.mstr(p, r4, fp)) : {FEb.get_show.p(c, st, b, _) == Wr.Got{FEb.QShow{c, st, b, p, m}, rest} : Wr.Dec<FEb.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(m, rest)), Wr.Got{m, rest}, Wire.wire_str_round_trip(m, rest, fm)) : {FEb.get_show.m(c, st, b, p, _) == Wr.Got{FEb.QShow{c, st, b, p, m}, rest} : Wr.Dec<FEb.Req>}
      {==}
    case FEb.QTruncate{+t, +cap}:
      +h0 = h
      +ft = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(t)), LawsBase.wire_fits(cap), h0)
      +fcap = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(t)), LawsBase.wire_fits(cap), h0)
      +r1 = Wr.put_nat(cap, rest)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(t, r1)), Wr.Got{t, r1}, Wire.wire_str_round_trip(t, r1, ft)) : {FEb.get_cut(_) == Wr.Got{FEb.QTruncate{t, cap}, rest} : Wr.Dec<FEb.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(cap, rest)), Wr.Got{cap, rest}, Wire.wire_nat_round_trip(cap, rest, fcap)) : {FEb.get_cut.max(t, _) == Wr.Got{FEb.QTruncate{t, cap}, rest} : Wr.Dec<FEb.Req>}
      {==}

def ErrorBody.error_body_entry_reads(q, rest, h):
  ebr.req(q, rest, h)

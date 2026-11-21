# eukhe: the proof of LAW gateway_report_entry_exact
#
# PROOF: each decoder of bend/ffi_gateway_report.bend answers Got{x, rest}
# only for an input that is the spec's spelling of x before rest, with x
# within the wire (grx.*: a predicate per decoder answer, carried stage by
# stage with the Nat and string exactness lemmas of the doc_commit entry,
# dcw.nat and dcw.str, and gateway_answer's Bool and Maybe predicates,
# gax.bool and gax.maybe). The entry answers a value only for a request
# read whole with nothing left: that input is the spelled request
# (grx.top).

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/gateway_report.bend as Gr
import ../../bend/ffi_gateway_answer.bend as FGa
import ../../bend/ffi_gateway_report.bend as FGr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_report.bend as GatewayReport
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../base/wire_dec.bend as LE
import ../gateway_answer/gateway_answer_entry_exact.bend as PGax

# Answers
# -------

def grx.AP(s: String, d: Wr.Dec<Ga.Answer>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == GatewayReport.gr_w_answer(a, r) : String} & {GatewayReport.gr_fit_answer(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def grx.text(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> grx.AP(s, FGr.get_text(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = sp
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(x, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_str(x, r), e)), f)
    case Wr.Bad{}:
      Unit{}

def grx.failed(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> grx.AP(s, FGr.get_failed(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = sp
      (Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_str(x, r)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_str(x, r), e)), f)
    case Wr.Bad{}:
      Unit{}

def grx.answer.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> grx.AP(s, FGr.get_answer.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      grx.text(s, s1, pre, Wr.get_str(s1), LE.dcw.str(s1))
    case 2n:
      grx.failed(s, s1, pre, Wr.get_str(s1), LE.dcw.str(s1))
    case 3n:
      (pre, {==})
    case 4n+u:
      Unit{}

def grx.answer.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> grx.AP(s, FGr.get_answer(d)):
  match d:
    case Wr.Got{t, s1}:
      grx.answer.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def grx.answer(+s: String) -> grx.AP(s, FGr.get_answer(Wr.get_nat(s))):
  grx.answer.go(s, Wr.get_nat(s), LE.dcw.nat(s))

# Ends
# ----

def grx.EP(s: String, d: Wr.Dec<Gr.End>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == GatewayReport.gr_w_end(e, r) : String} & {GatewayReport.gr_fit_end(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def grx.run.left(-s: String, +w: Bool, -s2: String, pre: {s == Wr.put_nat(1n, Wr.put_bool(w, s2)) : String}, d: Wr.Dec<Maybe<&2, String>>, mp: PGax.gax.MP(s2, d)) -> grx.EP(s, FGr.get_run.left(w, d)):
  match d:
    case Wr.Got{+l, +r}:
      (ee, f) = mp
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_bool(w, s2)), Wr.put_nat(1n, Wr.put_bool(w, GatewayAnswer.ga_w_maybe(l, r))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_bool(w, z)), s2, GatewayAnswer.ga_w_maybe(l, r), ee)), f)
    case Wr.Bad{}:
      Unit{}

def grx.run(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, bp: PGax.gax.BP(s1, d)) -> grx.EP(s, FGr.get_run(d)):
  match d:
    case Wr.Got{+w, +s2}:
      grx.run.left(s, w, s2, Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_bool(w, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_bool(w, s2), bp)), FGa.get_maybe(Wr.get_nat(s2)), PGax.gax.maybe(s2))
    case Wr.Bad{}:
      Unit{}

def grx.end.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> grx.EP(s, FGr.get_end.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      grx.run(s, s1, pre, Wr.get_bool(s1), PGax.gax.bool(s1))
    case 2n+u:
      Unit{}

def grx.end.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> grx.EP(s, FGr.get_end(d)):
  match d:
    case Wr.Got{t, s1}:
      grx.end.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def grx.end(+s: String) -> grx.EP(s, FGr.get_end(Wr.get_nat(s))):
  grx.end.go(s, Wr.get_nat(s), LE.dcw.nat(s))

# The request
# -----------

def grx.RP(s: String, d: Wr.Dec<FGr.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == GatewayReport.gr_w_req(q, r) : String} & {GatewayReport.gr_fit(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def grx.req.end(-s: String, +h: Ga.Answer, +a: Ga.Answer, -s2: String, pre: {s == GatewayReport.gr_w_answer(h, GatewayReport.gr_w_answer(a, s2)) : String}, fh: {GatewayReport.gr_fit_answer(h) == True{} : Bool}, fa: {GatewayReport.gr_fit_answer(a) == True{} : Bool}, d: Wr.Dec<Gr.End>, ep: grx.EP(s2, d)) -> grx.RP(s, FGr.get_req.end(h, a, d)):
  match d:
    case Wr.Got{+e, +r}:
      (ee, fe) = ep
      (Equal.trans(String, s, GatewayReport.gr_w_answer(h, GatewayReport.gr_w_answer(a, s2)), GatewayReport.gr_w_answer(h, GatewayReport.gr_w_answer(a, GatewayReport.gr_w_end(e, r))), pre, Equal.cong(String, String, z => GatewayReport.gr_w_answer(h, GatewayReport.gr_w_answer(a, z)), s2, GatewayReport.gr_w_end(e, r), ee)),
        LBool.cb_and_intro(GatewayReport.gr_fit_answer(h), Bool.and(GatewayReport.gr_fit_answer(a), GatewayReport.gr_fit_end(e)), fh, LBool.cb_and_intro(GatewayReport.gr_fit_answer(a), GatewayReport.gr_fit_end(e), fa, fe)))
    case Wr.Bad{}:
      Unit{}

def grx.req.answer(-s: String, +h: Ga.Answer, -s1: String, pre: {s == GatewayReport.gr_w_answer(h, s1) : String}, fh: {GatewayReport.gr_fit_answer(h) == True{} : Bool}, d: Wr.Dec<Ga.Answer>, ap: grx.AP(s1, d)) -> grx.RP(s, FGr.get_req.answer(h, d)):
  match d:
    case Wr.Got{+a, +s2}:
      (ea, fa) = ap
      grx.req.end(s, h, a, s2, Equal.trans(String, s, GatewayReport.gr_w_answer(h, s1), GatewayReport.gr_w_answer(h, GatewayReport.gr_w_answer(a, s2)), pre, Equal.cong(String, String, z => GatewayReport.gr_w_answer(h, z), s1, GatewayReport.gr_w_answer(a, s2), ea)), fh, fa, FGr.get_end(Wr.get_nat(s2)), grx.end(s2))
    case Wr.Bad{}:
      Unit{}

def grx.req.held(-s: String, d: Wr.Dec<Ga.Answer>, ap: grx.AP(s, d)) -> grx.RP(s, FGr.get_req.held(d)):
  match d:
    case Wr.Got{+h, +s1}:
      (eh, fh) = ap
      grx.req.answer(s, h, s1, eh, fh, FGr.get_answer(Wr.get_nat(s1)), grx.answer(s1))
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def grx.top(-s: String, d: Wr.Dec<FGr.Req>, rp: grx.RP(s, d), ok: {LawsBase.wire_opens_err(FGr.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FGr.Req, v => {s == GatewayReport.gr_w_req(v, "") : String} & {GatewayReport.gr_fit(v) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FGr.Req, v2 => {s == GatewayReport.gr_w_req(v2, "") : String} & {GatewayReport.gr_fit(v2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FGr.Req, v2 => {s == GatewayReport.gr_w_req(v2, "") : String} & {GatewayReport.gr_fit(v2) == True{} : Bool}>, ok)

def GatewayReport.gateway_report_entry_exact(s, ok):
  grx.top(s, FGr.get_req(s), grx.req.held(s, FGr.get_answer(Wr.get_nat(s)), grx.answer(s)), ok)

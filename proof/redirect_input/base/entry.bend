# eukhe: lemmas of the entry proofs of area redirect_input: the reply
# encoders are the spec spellers, a spelled request reads back (rie.*_rt),
# and a decoded one is spelled (rix.*: a predicate per decoder answer,
# carried stage by stage with the wire exactness lemmas dcw.nat, dcw.str)

import Base
import ../../../bend/redirect_input.bend as Ri
import ../../../bend/ffi_redirect_input.bend as FRi
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/redirect_input.bend as RedirectInput
import ../../base/wire_dec.bend as LE
import ../../base/staging.bend as LStg
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool

# Encoders
# --------

def rie.ms(m: Maybe<&2, String>, rest: String) -> {FRi.put_ms(m, rest) == RedirectInput.ri_w_ms(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def rie.fail(f: Ri.Fail) -> {FRi.put_fail(f) == RedirectInput.ri_w_fail(f, "") : String}:
  match f:
    case Ri.FMissing{}:
      {==}
    case Ri.FMismatch{}:
      {==}
    case Ri.FProvider{+e, +d}:
      %Equal.sym(String, FRi.put_ms(d, ""), RedirectInput.ri_w_ms(d, ""), rie.ms(d, "")) : {Wr.put_nat(2n, Wr.put_str(e, _)) == RedirectInput.ri_w_fail(Ri.FProvider{e, d}, "") : String}
      {==}

def rie.answer(a: Ri.Answer) -> {FRi.put_answer(a) == RedirectInput.ri_w_answer(a) : String}:
  match a:
    case Ri.Pasted{+c, +m}:
      %Equal.sym(String, FRi.put_ms(m, ""), RedirectInput.ri_w_ms(m, ""), rie.ms(m, "")) : {Wr.put_nat(0n, Wr.put_str(c, _)) == RedirectInput.ri_w_answer(Ri.Pasted{c, m}) : String}
      {==}
    case Ri.Failed{+f}:
      %Equal.sym(String, FRi.put_fail(f), RedirectInput.ri_w_fail(f, ""), rie.fail(f)) : {Wr.put_nat(1n, _) == RedirectInput.ri_w_answer(Ri.Failed{f}) : String}
      {==}

# Round trips
# -----------

def rie.ms_rt(m: Maybe<&2, String>, +rest: String, h: {RedirectInput.ri_fit_ms(m) == True{} : Bool}) -> {FRi.get_ms(RedirectInput.ri_w_ms(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FRi.get_ms.some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}

def rie.fail_rt(f: Ri.Fail, +rest: String, h: {RedirectInput.ri_fit_fail(f) == True{} : Bool}) -> {FRi.get_fail.start(Wr.get_nat(RedirectInput.ri_w_fail(f, rest))) == Wr.Got{f, rest} : Wr.Dec<Ri.Fail>}:
  match f:
    case Ri.FMissing{}:
      {==}
    case Ri.FMismatch{}:
      {==}
    case Ri.FProvider{+e, +d}:
      +h0 = h
      +he = LLogicBool.tree.pt.and_l(RedirectInput.ri_fit_str(e), RedirectInput.ri_fit_ms(d), h0)
      +hd = LLogicBool.tree.pt.and_r(RedirectInput.ri_fit_str(e), RedirectInput.ri_fit_ms(d), h0)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(e, RedirectInput.ri_w_ms(d, rest))), Wr.Got{e, RedirectInput.ri_w_ms(d, rest)}, Wire.wire_str_round_trip(e, RedirectInput.ri_w_ms(d, rest), he)) : {FRi.get_provider(_) == Wr.Got{Ri.FProvider{e, d}, rest} : Wr.Dec<Ri.Fail>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRi.get_ms(RedirectInput.ri_w_ms(d, rest)), Wr.Got{d, rest}, rie.ms_rt(d, rest, hd)) : {FRi.get_provider.desc(e, _) == Wr.Got{Ri.FProvider{e, d}, rest} : Wr.Dec<Ri.Fail>}
      {==}

def rie.req_rt(q: FRi.Req, +rest: String, h: {RedirectInput.ri_fit_req(q) == True{} : Bool}) -> {FRi.get_req(RedirectInput.ri_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FRi.Req>}:
  match q:
    case FRi.QClean{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FRi.get_clean(_) == Wr.Got{FRi.QClean{x}, rest} : Wr.Dec<FRi.Req>}
      {==}
    case FRi.QParse{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FRi.get_parse(_) == Wr.Got{FRi.QParse{x}, rest} : Wr.Dec<FRi.Req>}
      {==}
    case FRi.QNotice{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FRi.get_notice(_) == Wr.Got{FRi.QNotice{x}, rest} : Wr.Dec<FRi.Req>}
      {==}
    case FRi.QVerify{+c, +m, +e}:
      +h0 = h
      +hc = LLogicBool.tree.pt.and_l(RedirectInput.ri_fit_str(c), Bool.and(RedirectInput.ri_fit_ms(m), RedirectInput.ri_fit_str(e)), h0)
      +h1 = LLogicBool.tree.pt.and_r(RedirectInput.ri_fit_str(c), Bool.and(RedirectInput.ri_fit_ms(m), RedirectInput.ri_fit_str(e)), h0)
      +hm = LLogicBool.tree.pt.and_l(RedirectInput.ri_fit_ms(m), RedirectInput.ri_fit_str(e), h1)
      +he = LLogicBool.tree.pt.and_r(RedirectInput.ri_fit_ms(m), RedirectInput.ri_fit_str(e), h1)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(c, RedirectInput.ri_w_ms(m, Wr.put_str(e, rest)))), Wr.Got{c, RedirectInput.ri_w_ms(m, Wr.put_str(e, rest))}, Wire.wire_str_round_trip(c, RedirectInput.ri_w_ms(m, Wr.put_str(e, rest)), hc)) : {FRi.get_verify(_) == Wr.Got{FRi.QVerify{c, m, e}, rest} : Wr.Dec<FRi.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRi.get_ms(RedirectInput.ri_w_ms(m, Wr.put_str(e, rest))), Wr.Got{m, Wr.put_str(e, rest)}, rie.ms_rt(m, Wr.put_str(e, rest), hm)) : {FRi.get_verify.state(c, _) == Wr.Got{FRi.QVerify{c, m, e}, rest} : Wr.Dec<FRi.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(e, rest)), Wr.Got{e, rest}, Wire.wire_str_round_trip(e, rest, he)) : {FRi.get_verify.expected(c, m, _) == Wr.Got{FRi.QVerify{c, m, e}, rest} : Wr.Dec<FRi.Req>}
      {==}
    case FRi.QText{+f}:
      %Equal.sym(Wr.Dec<Ri.Fail>, FRi.get_fail.start(Wr.get_nat(RedirectInput.ri_w_fail(f, rest))), Wr.Got{f, rest}, rie.fail_rt(f, rest, h)) : {FRi.get_fail(_) == Wr.Got{FRi.QText{f}, rest} : Wr.Dec<FRi.Req>}
      {==}

# Replies never open with 'E'
# ---------------------------

def rie.answer_ok(a: Ri.Answer) -> {LawsBase.wire_opens_err(FRi.put_answer(a)) == False{} : Bool}:
  match a:
    case Ri.Pasted{c, m}:
      {==}
    case Ri.Failed{f}:
      {==}

def rie.reply_ok(q: FRi.Req) -> {LawsBase.wire_opens_err(FRi.answer(q)) == False{} : Bool}:
  match q:
    case FRi.QClean{x}:
      LE.dcw.sfin_ok(Wr.put_str.go(Ri.clean(x), SNil{}, 0n), "")
    case FRi.QParse{x}:
      rie.answer_ok(Ri.parse(x))
    case FRi.QVerify{c, m, e}:
      rie.answer_ok(Ri.verify(c, m, e))
    case FRi.QText{f}:
      LE.dcw.sfin_ok(Wr.put_str.go(Ri.text(f), SNil{}, 0n), "")
    case FRi.QNotice{x}:
      LE.dcw.sfin_ok(Wr.put_str.go(Ri.notice(x), SNil{}, 0n), "")

# Decoded requests are spelled
# ----------------------------

def rix.MS(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == RedirectInput.ri_w_ms(m, r) : String} & {RedirectInput.ri_fit_ms(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rix.ms_some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rix.MS(s, FRi.get_ms.some(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fit) = sp
      (LE.dcw.after(s, 1n, s1, Wr.put_str(x, r), pre, e), fit)
    case Wr.Bad{}:
      Unit{}

def rix.ms_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rix.MS(s, FRi.get_ms.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (np, {==})
        case 1n:
          rix.ms_some(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a Maybe<String> decoded is spelled, and fits
def rix.ms(+s: String) -> rix.MS(s, FRi.get_ms(s)):
  rix.ms_at(s, Wr.get_nat(s), LE.dcw.nat(s))

def rix.FP(s: String, d: Wr.Dec<Ri.Fail>) -> Type:
  match d:
    case Wr.Got{f, r}:
      {s == RedirectInput.ri_w_fail(f, r) : String} & {RedirectInput.ri_fit_fail(f) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rix.desc(-s: String, +e: String, -s2: String, pre: {s == Wr.put_nat(2n, Wr.put_str(e, s2)) : String}, fe: {RedirectInput.ri_fit_str(e) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, mp: rix.MS(s2, d)) -> rix.FP(s, FRi.get_provider.desc(e, d)):
  match d:
    case Wr.Got{+m, +r}:
      (e1, fm) = mp
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(e, s2)), Wr.put_nat(2n, Wr.put_str(e, RedirectInput.ri_w_ms(m, r))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(e, z)), s2, RedirectInput.ri_w_ms(m, r), e1)), LBool.cb_and_intro(RedirectInput.ri_fit_str(e), RedirectInput.ri_fit_ms(m), fe, fm))
    case Wr.Bad{}:
      Unit{}

def rix.provider(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rix.FP(s, FRi.get_provider(d)):
  match d:
    case Wr.Got{+e, +r}:
      (e1, fe) = sp
      rix.desc(s, e, r, LE.dcw.after(s, 2n, s1, Wr.put_str(e, r), pre, e1), fe, FRi.get_ms(r), rix.ms(r))
    case Wr.Bad{}:
      Unit{}

def rix.fail_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rix.FP(s, FRi.get_fail.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (np, {==})
        case 1n:
          (np, {==})
        case 2n:
          rix.provider(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rix.RP(s: String, d: Wr.Dec<FRi.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == RedirectInput.ri_w_req(q, r) : String} & {RedirectInput.ri_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rix.clean(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rix.RP(s, FRi.get_clean(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fx) = sp
      (LE.dcw.after(s, 0n, s1, Wr.put_str(x, r), pre, e), fx)
    case Wr.Bad{}:
      Unit{}

def rix.parse(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rix.RP(s, FRi.get_parse(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fx) = sp
      (LE.dcw.after(s, 1n, s1, Wr.put_str(x, r), pre, e), fx)
    case Wr.Bad{}:
      Unit{}

def rix.notice(-s: String, -s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rix.RP(s, FRi.get_notice(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fx) = sp
      (LE.dcw.after(s, 4n, s1, Wr.put_str(x, r), pre, e), fx)
    case Wr.Bad{}:
      Unit{}

def rix.vexp(-s: String, +c: String, +m: Maybe<&2, String>, -s3: String, pre: {s == Wr.put_nat(2n, Wr.put_str(c, RedirectInput.ri_w_ms(m, s3))) : String}, +fcm: {Bool.and(RedirectInput.ri_fit_str(c), RedirectInput.ri_fit_ms(m)) == True{} : Bool}, d: Wr.Dec<String>, sp: LE.dcw.SP(s3, d)) -> rix.RP(s, FRi.get_verify.expected(c, m, d)):
  match d:
    case Wr.Got{+e, +r}:
      (e1, fe) = sp
      +fc = LLogicBool.tree.pt.and_l(RedirectInput.ri_fit_str(c), RedirectInput.ri_fit_ms(m), fcm)
      +fm = LLogicBool.tree.pt.and_r(RedirectInput.ri_fit_str(c), RedirectInput.ri_fit_ms(m), fcm)
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(c, RedirectInput.ri_w_ms(m, s3))), Wr.put_nat(2n, Wr.put_str(c, RedirectInput.ri_w_ms(m, Wr.put_str(e, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(c, RedirectInput.ri_w_ms(m, z))), s3, Wr.put_str(e, r), e1)),
        LBool.cb_and_intro(RedirectInput.ri_fit_str(c), Bool.and(RedirectInput.ri_fit_ms(m), RedirectInput.ri_fit_str(e)), fc, LBool.cb_and_intro(RedirectInput.ri_fit_ms(m), RedirectInput.ri_fit_str(e), fm, fe)))
    case Wr.Bad{}:
      Unit{}

def rix.vstate(-s: String, +c: String, -s2: String, pre: {s == Wr.put_nat(2n, Wr.put_str(c, s2)) : String}, fc: {RedirectInput.ri_fit_str(c) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, mp: rix.MS(s2, d)) -> rix.RP(s, FRi.get_verify.state(c, d)):
  match d:
    case Wr.Got{+m, +r}:
      (e1, fm) = mp
      +pre2 = Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(c, s2)), Wr.put_nat(2n, Wr.put_str(c, RedirectInput.ri_w_ms(m, r))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(c, z)), s2, RedirectInput.ri_w_ms(m, r), e1))
      rix.vexp(s, c, m, r, pre2, LBool.cb_and_intro(RedirectInput.ri_fit_str(c), RedirectInput.ri_fit_ms(m), fc, fm), Wr.get_str(r), LE.dcw.str(r))
    case Wr.Bad{}:
      Unit{}

def rix.verify(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> rix.RP(s, FRi.get_verify(d)):
  match d:
    case Wr.Got{+c, +r}:
      (e1, fc) = sp
      rix.vstate(s, c, r, LE.dcw.after(s, 2n, s1, Wr.put_str(c, r), pre, e1), fc, FRi.get_ms(r), rix.ms(r))
    case Wr.Bad{}:
      Unit{}

def rix.text(-s: String, -s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Ri.Fail>, fp: rix.FP(s1, d)) -> rix.RP(s, FRi.get_fail(d)):
  match d:
    case Wr.Got{+f, +r}:
      (e1, ff) = fp
      (LE.dcw.after(s, 3n, s1, RedirectInput.ri_w_fail(f, r), pre, e1), ff)
    case Wr.Bad{}:
      Unit{}

def rix.req_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> rix.RP(s, FRi.get_req.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          rix.clean(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 1n:
          rix.parse(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 2n:
          rix.verify(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 3n:
          rix.text(s, s1, np, FRi.get_fail.start(Wr.get_nat(s1)), rix.fail_at(s1, Wr.get_nat(s1), LE.dcw.nat(s1)))
        case 4n:
          rix.notice(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 5n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rix.T(s: String) -> Type:
  Sigma<&1, &1, FRi.Req, q => {s == RedirectInput.ri_w_req(q, "") : String} & {RedirectInput.ri_fit_req(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def rix.top(-s: String, d: Wr.Dec<FRi.Req>, rp: rix.RP(s, d), ok: {LawsBase.wire_opens_err(FRi.ffi.got(d)) == False{} : Bool}) -> rix.T(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(rix.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(rix.T(s), ok)

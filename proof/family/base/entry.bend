# eukhe: lemmas of the entry proofs of area family: a spelled request
# reads back (fe.req_rt), the reply encoder spells the spec's decision
# (fe.reply), no reply opens with 'E' (fe.answer_ok), and a decoded
# request is spelled (fx.*: a predicate per decoder stage, carried with
# the wire exactness laws wire_nat_exact and the list lemmas of
# proof/base/wire_strs.bend)

import Base
import ../../../bend/family.bend as F
import ../../../bend/ffi_family.bend as FF
import ../../../bend/wire.bend as Wr
import ../../../spec/rlm/family.bend as FamSpec
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/doc_commit.bend as DocCommit
import ../../../laws/family.bend as Family
import ../../base/wire_strs.bend as LS
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool
import ../../base/staging.bend as LStg
import ../family_refusal_precedence.bend as PFamilyRefusalPrecedence
import ../family_text_spec.bend as PFamilyTextSpec

# The whys
# --------

def fe.strs(ws: List<&2, String>, -rest: String) -> {Family.fam_w_strs(ws, rest) == LS.dcw.strs.items(ws, rest) : String}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      Equal.cong(String, String, z => Wr.put_str(w, z), Family.fam_w_strs(t, rest), LS.dcw.strs.items(t, rest), fe.strs(t, rest))

def fe.fit(ws: List<&2, String>) -> {Family.fam_fit_strs(ws) == DocCommit.sp_fit_strs(ws) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      Equal.cong(Bool, Bool, z => Bool.and(LawsBase.wire_fits(String.length(w)), z), Family.fam_fit_strs(t), DocCommit.sp_fit_strs(t), fe.fit(t))

def fe.fit_to(+ws: List<&2, String>, h: {Family.fam_fit_strs(ws) == True{} : Bool}) -> {DocCommit.sp_fit_strs(ws) == True{} : Bool}:
  Equal.trans(Bool, DocCommit.sp_fit_strs(ws), Family.fam_fit_strs(ws), True{}, Equal.sym(Bool, Family.fam_fit_strs(ws), DocCommit.sp_fit_strs(ws), fe.fit(ws)), h)

def fe.fit_back(+ws: List<&2, String>, h: {DocCommit.sp_fit_strs(ws) == True{} : Bool}) -> {Family.fam_fit_strs(ws) == True{} : Bool}:
  Equal.trans(Bool, Family.fam_fit_strs(ws), DocCommit.sp_fit_strs(ws), True{}, fe.fit(ws), h)

# a list of whys is its count, then each why
def fe.list(+ws: List<&2, String>, +rest: String) -> {Wr.put_list(~String, ~Wr.put_str, ws, rest) == Wr.put_nat(List.length(&2, String, ws), Family.fam_w_strs(ws, rest)) : String}:
  Equal.trans(String, Wr.put_list(~String, ~Wr.put_str, ws, rest), Wr.put_nat(List.length(&2, String, ws), LS.dcw.strs.items(ws, rest)), Wr.put_nat(List.length(&2, String, ws), Family.fam_w_strs(ws, rest)), LS.dcw.strs.put(ws, rest), Equal.cong(String, String, z => Wr.put_nat(List.length(&2, String, ws), z), LS.dcw.strs.items(ws, rest), Family.fam_w_strs(ws, rest), Equal.sym(String, Family.fam_w_strs(ws, rest), LS.dcw.strs.items(ws, rest), fe.strs(ws, rest))))

# Round trip
# ----------

def fe.req_rt(q: FF.Req, +rest: String, h: {Family.fam_fit_req(q) == True{} : Bool}) -> {FF.get_req(Family.fam_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FF.Req>}:
  match q:
    case FF.Req{+d, +m, +r, +c, +ws}:
      +h0 = h
      +fd = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(d), Bool.and(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws))))), h0)
      +h1 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(d), Bool.and(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws))))), h0)
      +fm = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws)))), h1)
      +h2 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws)))), h1)
      +fr = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws))), h2)
      +h3 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws))), h2)
      +fc = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws)), h3)
      +h4 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws)), h3)
      +fn = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws), h4)
      +fs = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws), h4)
      +w4 = Wr.put_nat(List.length(&2, String, ws), Family.fam_w_strs(ws, rest))
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(d, Wr.put_nat(m, Wr.put_nat(r, Wr.put_nat(c, w4))))), Wr.Got{d, Wr.put_nat(m, Wr.put_nat(r, Wr.put_nat(c, w4)))}, Wire.wire_nat_round_trip(d, Wr.put_nat(m, Wr.put_nat(r, Wr.put_nat(c, w4))), fd)) : {FF.get_req.depth(_) == Wr.Got{FF.Req{d, m, r, c, ws}, rest} : Wr.Dec<FF.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(m, Wr.put_nat(r, Wr.put_nat(c, w4)))), Wr.Got{m, Wr.put_nat(r, Wr.put_nat(c, w4))}, Wire.wire_nat_round_trip(m, Wr.put_nat(r, Wr.put_nat(c, w4)), fm)) : {FF.get_req.max(d, _) == Wr.Got{FF.Req{d, m, r, c, ws}, rest} : Wr.Dec<FF.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(r, Wr.put_nat(c, w4))), Wr.Got{r, Wr.put_nat(c, w4)}, Wire.wire_nat_round_trip(r, Wr.put_nat(c, w4), fr)) : {FF.get_req.running(d, m, _) == Wr.Got{FF.Req{d, m, r, c, ws}, rest} : Wr.Dec<FF.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(c, w4)), Wr.Got{c, w4}, Wire.wire_nat_round_trip(c, w4, fc)) : {FF.get_req.cap(d, m, r, _) == Wr.Got{FF.Req{d, m, r, c, ws}, rest} : Wr.Dec<FF.Req>}
      %fe.list(ws, rest) : {FF.get_req.whys(d, m, r, c, Wr.get_list(~String, ~Wr.get_str, _)) == Wr.Got{FF.Req{d, m, r, c, ws}, rest} : Wr.Dec<FF.Req>}
      %LS.dcw.strs.back(ws, rest, fn, fe.fit_to(ws, fs)) : {FF.get_req.whys(d, m, r, c, _) == Wr.Got{FF.Req{d, m, r, c, ws}, rest} : Wr.Dec<FF.Req>}
      {==}

# Replies
# -------

def fe.verdict(+d: Nat, +m: Nat, v: F.Verdict) -> {FF.put_verdict(d, m, v) == Family.fam_w_verdict(d, m, v) : String}:
  match v:
    case F.Admit{k}:
      {==}
    case F.Refuse{+f}:
      %Family.family_text_spec(d, m, f) : {Wr.put_nat(1n, Wr.put_str(F.text(d, m, f), "")) == Wr.put_nat(1n, Wr.put_str(_, "")) : String}
      {==}

# the entry's answer is the spec's decision, spelled
def fe.reply(q: FF.Req) -> {FF.answer(q) == Family.fam_w_reply(q) : String}:
  match q:
    case FF.Req{+d, +m, +r, +c, +ws}:
      %Family.family_refusal_precedence(d, m, r, c, ws) : {FF.put_verdict(d, m, F.decide(d, m, r, c, ws)) == Family.fam_w_verdict(d, m, _) : String}
      fe.verdict(d, m, F.decide(d, m, r, c, ws))

def fe.verdict_ok(+d: Nat, +m: Nat, v: F.Verdict) -> {LawsBase.wire_opens_err(FF.put_verdict(d, m, v)) == False{} : Bool}:
  match v:
    case F.Admit{k}:
      {==}
    case F.Refuse{f}:
      {==}

# no answer opens with 'E'
def fe.answer_ok(q: FF.Req) -> {LawsBase.wire_opens_err(FF.answer(q)) == False{} : Bool}:
  match q:
    case FF.Req{+d, +m, r, c, ws}:
      fe.verdict_ok(d, m, F.decide(d, m, r, c, ws))

# Decoded requests are spelled
# ----------------------------

def fx.RP(s: String, x: Wr.Dec<FF.Req>) -> Type:
  match x:
    case Wr.Got{q, rr}:
      {s == Family.fam_w_req(q, rr) : String} & {Family.fam_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def fx.whys(-s: String, +d: Nat, +m: Nat, +r: Nat, +c: Nat, -s4: String, pre: {s == Wr.put_nat(d, Wr.put_nat(m, Wr.put_nat(r, Wr.put_nat(c, s4)))) : String}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, fm: {LawsBase.wire_fits(m) == True{} : Bool}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, x: Wr.Dec<List<&2, String>>, ls: LS.dcw.strs.LS(s4, x)) -> fx.RP(s, FF.get_req.whys(d, m, r, c, x)):
  match x:
    case Wr.Got{+ws, +rr}:
      (e1, f23) = ls
      (fn, ff) = f23
      +e2 = Equal.trans(String, s4, Wr.put_list(~String, ~Wr.put_str, ws, rr), Wr.put_nat(List.length(&2, String, ws), Family.fam_w_strs(ws, rr)), e1, fe.list(ws, rr))
      (Equal.trans(String, s, Wr.put_nat(d, Wr.put_nat(m, Wr.put_nat(r, Wr.put_nat(c, s4)))), Wr.put_nat(d, Wr.put_nat(m, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(List.length(&2, String, ws), Family.fam_w_strs(ws, rr)))))), pre, Equal.cong(String, String, z => Wr.put_nat(d, Wr.put_nat(m, Wr.put_nat(r, Wr.put_nat(c, z)))), s4, Wr.put_nat(List.length(&2, String, ws), Family.fam_w_strs(ws, rr)), e2)),
        LBool.cb_and_intro(LawsBase.wire_fits(d), Bool.and(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws))))), fd,
          LBool.cb_and_intro(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws)))), fm,
            LBool.cb_and_intro(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws))), fr,
              LBool.cb_and_intro(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws)), fc,
                LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, String, ws)), Family.fam_fit_strs(ws), fn, fe.fit_back(ws, ff)))))))
    case Wr.Bad{}:
      Unit{}

def fx.cap(-s: String, +d: Nat, +m: Nat, +r: Nat, +s3: String, pre: {s == Wr.put_nat(d, Wr.put_nat(m, Wr.put_nat(r, s3))) : String}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, fm: {LawsBase.wire_fits(m) == True{} : Bool}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == x : Wr.Dec<Nat>}) -> fx.RP(s, FF.get_req.cap(d, m, r, x)):
  match x:
    case Wr.Got{+c, +s4}:
      +e = ed
      +ec = Wire.wire_nat_exact(s3, c, s4, e)
      +fc = Wire.wire_nat_decoded_fits(s3, c, s4, e)
      +pre2 = Equal.trans(String, s, Wr.put_nat(d, Wr.put_nat(m, Wr.put_nat(r, s3))), Wr.put_nat(d, Wr.put_nat(m, Wr.put_nat(r, Wr.put_nat(c, s4)))), pre, Equal.cong(String, String, z => Wr.put_nat(d, Wr.put_nat(m, Wr.put_nat(r, z))), s3, Wr.put_nat(c, s4), ec))
      fx.whys(s, d, m, r, c, s4, pre2, fd, fm, fr, fc, Wr.get_list(~String, ~Wr.get_str, s4), LS.dcw.strs.list(s4))
    case Wr.Bad{}:
      Unit{}

def fx.running(-s: String, +d: Nat, +m: Nat, +s2: String, pre: {s == Wr.put_nat(d, Wr.put_nat(m, s2)) : String}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, fm: {LawsBase.wire_fits(m) == True{} : Bool}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == x : Wr.Dec<Nat>}) -> fx.RP(s, FF.get_req.running(d, m, x)):
  match x:
    case Wr.Got{+r, +s3}:
      +e = ed
      +er = Wire.wire_nat_exact(s2, r, s3, e)
      +fr = Wire.wire_nat_decoded_fits(s2, r, s3, e)
      +pre2 = Equal.trans(String, s, Wr.put_nat(d, Wr.put_nat(m, s2)), Wr.put_nat(d, Wr.put_nat(m, Wr.put_nat(r, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(d, Wr.put_nat(m, z)), s2, Wr.put_nat(r, s3), er))
      fx.cap(s, d, m, r, s3, pre2, fd, fm, fr, Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def fx.max(-s: String, +d: Nat, +s1: String, pre: {s == Wr.put_nat(d, s1) : String}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == x : Wr.Dec<Nat>}) -> fx.RP(s, FF.get_req.max(d, x)):
  match x:
    case Wr.Got{+m, +s2}:
      +e = ed
      +em = Wire.wire_nat_exact(s1, m, s2, e)
      +fm = Wire.wire_nat_decoded_fits(s1, m, s2, e)
      +pre2 = Equal.trans(String, s, Wr.put_nat(d, s1), Wr.put_nat(d, Wr.put_nat(m, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(d, z), s1, Wr.put_nat(m, s2), em))
      fx.running(s, d, m, s2, pre2, fd, fm, Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def fx.depth(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> fx.RP(s, FF.get_req.depth(x)):
  match x:
    case Wr.Got{+d, +s1}:
      +e = ed
      fx.max(s, d, s1, Wire.wire_nat_exact(s, d, s1, e), Wire.wire_nat_decoded_fits(s, d, s1, e), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and fits
def fx.req(+s: String) -> fx.RP(s, FF.get_req(s)):
  fx.depth(s, Wr.get_nat(s), {==})

def fx.T(s: String) -> Type:
  Sigma<&1, &1, FF.Req, q => {s == Family.fam_w_req(q, "") : String} & {Family.fam_fit_req(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def fx.top(-s: String, x: Wr.Dec<FF.Req>, rp: fx.RP(s, x), ok: {LawsBase.wire_opens_err(FF.ffi.got(x)) == False{} : Bool}) -> fx.T(s):
  match x:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{y, z}:
          LStg.stg.absurd(fx.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(fx.T(s), ok)

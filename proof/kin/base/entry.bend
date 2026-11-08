# eukhe: lemmas of the entry proofs of area kin: a spelled request reads
# back (ke.req_rt), the reply encoder spells the spec's decision and
# landing (ke.answer), no reply opens with 'E' (ke.answer_ok), and a
# decoded request is spelled (kx.*: a predicate per decoder stage, carried
# with the wire exactness lemmas of proof/base/wire_dec.bend and the list
# lemmas of proof/base/wire_strs.bend)

import Base
import ../../../bend/kin.bend as K
import ../../../bend/ffi_kin.bend as FK
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/doc_commit.bend as DocCommit
import ../../../laws/kin.bend as Kin
import ../../base/wire_dec.bend as LD
import ../../base/wire_strs.bend as LS
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool
import ../../base/staging.bend as LStg

# The edge columns
# ----------------

def ke.fit(xs: List<&2, String>) -> {Kin.kin_fit_strs(xs) == DocCommit.sp_fit_strs(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(Bool, Bool, z => Bool.and(LawsBase.wire_fits(String.length(x)), z), Kin.kin_fit_strs(t), DocCommit.sp_fit_strs(t), ke.fit(t))

def ke.fit_to(+xs: List<&2, String>, h: {Kin.kin_fit_strs(xs) == True{} : Bool}) -> {DocCommit.sp_fit_strs(xs) == True{} : Bool}:
  Equal.trans(Bool, DocCommit.sp_fit_strs(xs), Kin.kin_fit_strs(xs), True{}, Equal.sym(Bool, Kin.kin_fit_strs(xs), DocCommit.sp_fit_strs(xs), ke.fit(xs)), h)

def ke.fit_back(+xs: List<&2, String>, h: {DocCommit.sp_fit_strs(xs) == True{} : Bool}) -> {Kin.kin_fit_strs(xs) == True{} : Bool}:
  Equal.trans(Bool, Kin.kin_fit_strs(xs), DocCommit.sp_fit_strs(xs), True{}, ke.fit(xs), h)

# Round trip
# ----------

def ke.req_rt(q: FK.Req, +rest: String, h: {Kin.kin_fit_req(q) == True{} : Bool}) -> {FK.get_req(Kin.kin_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FK.Req>}:
  match q:
    case FK.QAdmit{+sn, +tg, +cs, +ps}:
      +h0 = h
      +fs = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(sn)), Bool.and(LawsBase.wire_fits(String.length(tg)), Bool.and(LawsBase.wire_fits(List.length(&2, String, cs)), Bool.and(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps))))), h0)
      +h1 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(sn)), Bool.and(LawsBase.wire_fits(String.length(tg)), Bool.and(LawsBase.wire_fits(List.length(&2, String, cs)), Bool.and(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps))))), h0)
      +ft = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(tg)), Bool.and(LawsBase.wire_fits(List.length(&2, String, cs)), Bool.and(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps)))), h1)
      +h2 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(tg)), Bool.and(LawsBase.wire_fits(List.length(&2, String, cs)), Bool.and(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps)))), h1)
      +fnc = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(List.length(&2, String, cs)), Bool.and(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps))), h2)
      +h3 = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(List.length(&2, String, cs)), Bool.and(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps))), h2)
      +fsc = LLogicBool.tree.pt.and_l(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps)), h3)
      +h4 = LLogicBool.tree.pt.and_r(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps)), h3)
      +fnp = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps), h4)
      +fsp = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps), h4)
      +lp = Wr.put_list(~String, ~Wr.put_str, ps, rest)
      +lc = Wr.put_list(~String, ~Wr.put_str, cs, lp)
      %LD.dcw.str_back(sn, Wr.put_str(tg, lc), fs) : {FK.get_admit(_) == Wr.Got{FK.QAdmit{sn, tg, cs, ps}, rest} : Wr.Dec<FK.Req>}
      %LD.dcw.str_back(tg, lc, ft) : {FK.get_admit.target(sn, _) == Wr.Got{FK.QAdmit{sn, tg, cs, ps}, rest} : Wr.Dec<FK.Req>}
      %LS.dcw.strs.back(cs, lp, fnc, ke.fit_to(cs, fsc)) : {FK.get_admit.children(sn, tg, _) == Wr.Got{FK.QAdmit{sn, tg, cs, ps}, rest} : Wr.Dec<FK.Req>}
      %LS.dcw.strs.back(ps, rest, fnp, ke.fit_to(ps, fsp)) : {FK.get_admit.parents(sn, tg, cs, _) == Wr.Got{FK.QAdmit{sn, tg, cs, ps}, rest} : Wr.Dec<FK.Req>}
      {==}
    case FK.QLand{st}:
      match st:
        case K.Busy{}:
          {==}
        case K.Idle{}:
          {==}
        case K.Parked{}:
          {==}

# Replies
# -------

def ke.verdict(v: K.Verdict) -> {FK.put_verdict(v) == Kin.kin_w_verdict(v) : String}:
  match v:
    case K.Admit{r}:
      match r:
        case K.Parent{}:
          {==}
        case K.Child{}:
          {==}
    case K.Refuse{f}:
      match f:
        case K.SelfMessage{}:
          {==}
        case K.NotKin{}:
          {==}

# the entry's answer is the core's decision or landing, spelled as the
# laws spell it
def ke.answer(q: FK.Req) -> {FK.answer(q) == Kin.kin_w_reply(q) : String}:
  match q:
    case FK.QAdmit{sn, tg, cs, ps}:
      ke.verdict(K.decide(sn, tg, cs, ps))
    case FK.QLand{st}:
      match st:
        case K.Busy{}:
          {==}
        case K.Idle{}:
          {==}
        case K.Parked{}:
          {==}

def ke.verdict_ok(v: K.Verdict) -> {LawsBase.wire_opens_err(FK.put_verdict(v)) == False{} : Bool}:
  match v:
    case K.Admit{r}:
      {==}
    case K.Refuse{f}:
      {==}

# no answer opens with 'E'
def ke.answer_ok(q: FK.Req) -> {LawsBase.wire_opens_err(FK.answer(q)) == False{} : Bool}:
  match q:
    case FK.QAdmit{sn, tg, cs, ps}:
      ke.verdict_ok(K.decide(sn, tg, cs, ps))
    case FK.QLand{st}:
      match st:
        case K.Busy{}:
          {==}
        case K.Idle{}:
          {==}
        case K.Parked{}:
          {==}

# Decoded requests are spelled
# ----------------------------

def kx.RP(s: String, x: Wr.Dec<FK.Req>) -> Type:
  match x:
    case Wr.Got{q, rr}:
      {s == Kin.kin_w_req(q, rr) : String} & {Kin.kin_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def kx.parents(-s: String, +sn: String, +tg: String, +cs: List<&2, String>, -s3: String, pre: {s == Wr.put_nat(0n, Wr.put_str(sn, Wr.put_str(tg, Wr.put_list(~String, ~Wr.put_str, cs, s3)))) : String}, fs: {LawsBase.wire_fits(String.length(sn)) == True{} : Bool}, ft: {LawsBase.wire_fits(String.length(tg)) == True{} : Bool}, fnc: {LawsBase.wire_fits(List.length(&2, String, cs)) == True{} : Bool}, fsc: {DocCommit.sp_fit_strs(cs) == True{} : Bool}, x: Wr.Dec<List<&2, String>>, ls: LS.dcw.strs.LS(s3, x)) -> kx.RP(s, FK.get_admit.parents(sn, tg, cs, x)):
  match x:
    case Wr.Got{+ps, +rr}:
      (e, f2) = ls
      (fnp, fsp) = f2
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_str(sn, Wr.put_str(tg, Wr.put_list(~String, ~Wr.put_str, cs, s3)))), Wr.put_nat(0n, Wr.put_str(sn, Wr.put_str(tg, Wr.put_list(~String, ~Wr.put_str, cs, Wr.put_list(~String, ~Wr.put_str, ps, rr))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_str(sn, Wr.put_str(tg, Wr.put_list(~String, ~Wr.put_str, cs, z)))), s3, Wr.put_list(~String, ~Wr.put_str, ps, rr), e)),
        LBool.cb_and_intro(LawsBase.wire_fits(String.length(sn)), Bool.and(LawsBase.wire_fits(String.length(tg)), Bool.and(LawsBase.wire_fits(List.length(&2, String, cs)), Bool.and(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps))))), fs,
          LBool.cb_and_intro(LawsBase.wire_fits(String.length(tg)), Bool.and(LawsBase.wire_fits(List.length(&2, String, cs)), Bool.and(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps)))), ft,
            LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, String, cs)), Bool.and(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps))), fnc,
              LBool.cb_and_intro(Kin.kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps)), ke.fit_back(cs, fsc),
                LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, String, ps)), Kin.kin_fit_strs(ps), fnp, ke.fit_back(ps, fsp)))))))
    case Wr.Bad{}:
      Unit{}

def kx.children(-s: String, +sn: String, +tg: String, -s2: String, pre: {s == Wr.put_nat(0n, Wr.put_str(sn, Wr.put_str(tg, s2))) : String}, fs: {LawsBase.wire_fits(String.length(sn)) == True{} : Bool}, ft: {LawsBase.wire_fits(String.length(tg)) == True{} : Bool}, x: Wr.Dec<List<&2, String>>, ls: LS.dcw.strs.LS(s2, x)) -> kx.RP(s, FK.get_admit.children(sn, tg, x)):
  match x:
    case Wr.Got{+cs, +s3}:
      (e, f2) = ls
      (fnc, fsc) = f2
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, Wr.put_str(sn, Wr.put_str(tg, s2))), Wr.put_nat(0n, Wr.put_str(sn, Wr.put_str(tg, Wr.put_list(~String, ~Wr.put_str, cs, s3)))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_str(sn, Wr.put_str(tg, z))), s2, Wr.put_list(~String, ~Wr.put_str, cs, s3), e))
      kx.parents(s, sn, tg, cs, s3, pre2, fs, ft, fnc, fsc, FK.get_strs(s3), LS.dcw.strs.list(s3))
    case Wr.Bad{}:
      Unit{}

def kx.target(-s: String, +sn: String, -s1: String, pre: {s == Wr.put_nat(0n, Wr.put_str(sn, s1)) : String}, fs: {LawsBase.wire_fits(String.length(sn)) == True{} : Bool}, x: Wr.Dec<String>, sp: LD.dcw.SP(s1, x)) -> kx.RP(s, FK.get_admit.target(sn, x)):
  match x:
    case Wr.Got{+tg, +s2}:
      (e, ft) = sp
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, Wr.put_str(sn, s1)), Wr.put_nat(0n, Wr.put_str(sn, Wr.put_str(tg, s2))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_str(sn, z)), s1, Wr.put_str(tg, s2), e))
      kx.children(s, sn, tg, s2, pre2, fs, ft, FK.get_strs(s2), LS.dcw.strs.list(s2))
    case Wr.Bad{}:
      Unit{}

def kx.sender(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, x: Wr.Dec<String>, sp: LD.dcw.SP(s1, x)) -> kx.RP(s, FK.get_admit(x)):
  match x:
    case Wr.Got{+sn, +s2}:
      (e, fs) = sp
      kx.target(s, sn, s2, LD.dcw.after(s, 0n, s1, Wr.put_str(sn, s2), pre, e), fs, Wr.get_str(s2), LD.dcw.str(s2))
    case Wr.Bad{}:
      Unit{}

def kx.land.of(n: Nat, +r: String, -s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, en: {s1 == Wr.put_nat(n, r) : String}) -> kx.RP(s, FK.get_land.of(n, r)):
  match n:
    case 0n:
      (LD.dcw.after(s, 1n, s1, Wr.put_nat(0n, r), pre, en), {==})
    case 1n:
      (LD.dcw.after(s, 1n, s1, Wr.put_nat(1n, r), pre, en), {==})
    case 2n:
      (LD.dcw.after(s, 1n, s1, Wr.put_nat(2n, r), pre, en), {==})
    case 3n+u:
      Unit{}

def kx.land(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, x: Wr.Dec<Nat>, np: LD.dcw.NP(s1, x)) -> kx.RP(s, FK.get_land(x)):
  match x:
    case Wr.Got{+n, +r}:
      kx.land.of(n, r, s, s1, pre, np)
    case Wr.Bad{}:
      Unit{}

def kx.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> kx.RP(s, FK.get_req.tag(t, s1)):
  match t:
    case 0n:
      kx.sender(s, s1, pre, Wr.get_str(s1), LD.dcw.str(s1))
    case 1n:
      kx.land(s, s1, pre, Wr.get_nat(s1), LD.dcw.nat(s1))
    case 2n+u:
      Unit{}

# a request decoded is spelled, and fits
def kx.go(-s: String, d: Wr.Dec<Nat>, np: LD.dcw.NP(s, d)) -> kx.RP(s, FK.get_req.start(d)):
  match d:
    case Wr.Got{t, s1}:
      kx.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def kx.T(s: String) -> Type:
  Sigma<&1, &1, FK.Req, q => {s == Kin.kin_w_req(q, "") : String} & {Kin.kin_fit_req(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def kx.top(-s: String, x: Wr.Dec<FK.Req>, rp: kx.RP(s, x), ok: {LawsBase.wire_opens_err(FK.ffi.got(x)) == False{} : Bool}) -> kx.T(s):
  match x:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{y, z}:
          LStg.stg.absurd(kx.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(kx.T(s), ok)

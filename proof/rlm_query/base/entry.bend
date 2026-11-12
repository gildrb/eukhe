# eukhe: lemmas of the entry proofs of area rlm_query
# (bend/ffi_rlm_query.bend): a spelled request reads back (re.req_rt), the
# answer is the spec's decision spelled (re.reply), no answer opens with
# 'E' (re.answer_ok), and each decoder stage answers Got only for the
# spelling of what it read so far, every number, count and length within
# the wire (re.x.*: the stage carries `pre`, the input spelled up to its
# field, and extends it with the field's exactness law; a list of Nats
# fits by re.nats_fit)

import Base
import ../../../bend/rlm_query.bend as Rq
import ../../../bend/ffi_rlm_query.bend as FRq
import ../../../bend/wire.bend as Wr
import ../../../spec/rlm/query.bend as QSpec
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/rlm_query.bend as RlmQuery
import ../../base/wire_dec.bend as LE
import ../../base/wire.bend as LWire
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../../wire/wire_list_exact.bend as PWireListExact
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ./nat.bend as LN
import ./plan.bend as LP
import ./cut.bend as LC

# Round trip
# ----------

# a spelled request that fits reads back, the rest untouched
def re.req_rt(q: FRq.Req, +rest: String, h: {RlmQuery.rq_fit_req(q) == True{} : Bool}) -> {FRq.get_req(RlmQuery.rq_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FRq.Req>}:
  match q:
    case FRq.QPlan{+r, +c, +w, +b, +u, +ss}:
      +fl = Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ss)), LawsBase.wire_nats_fit(ss))
      +h0 = h
      +fr = LP.qw.and_l(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl)))), h0)
      +h1 = LP.qw.and_r(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl)))), h0)
      +fc = LP.qw.and_l(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl))), h1)
      +h2 = LP.qw.and_r(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl))), h1)
      +fw = LP.qw.and_l(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl)), h2)
      +h3 = LP.qw.and_r(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl)), h2)
      +fb = LP.qw.and_l(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl), h3)
      +h4 = LP.qw.and_r(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl), h3)
      +fu = LP.qw.and_l(LawsBase.wire_fits(u), fl, h4)
      +fs = LP.qw.and_r(LawsBase.wire_fits(u), fl, h4)
      +s5 = Wr.put_list(~Nat, ~Wr.put_nat, ss, rest)
      +goal = {Wr.Got{FRq.QPlan{r, c, w, b, u, ss}, rest} : Wr.Dec<FRq.Req>}
      %Wire.wire_nats_spells(ss, rest) : {FRq.get_plan(Wr.get_nat(Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, _))))))) == goal : Wr.Dec<FRq.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, s5)))))), Wr.Got{r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, s5))))}, Wire.wire_nat_round_trip(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, s5)))), fr)) : {FRq.get_plan(_) == goal : Wr.Dec<FRq.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, s5))))), Wr.Got{c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, s5)))}, Wire.wire_nat_round_trip(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, s5))), fc)) : {FRq.get_plan.cap(r, _) == goal : Wr.Dec<FRq.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, s5)))), Wr.Got{w, Wr.put_nat(b, Wr.put_nat(u, s5))}, Wire.wire_nat_round_trip(w, Wr.put_nat(b, Wr.put_nat(u, s5)), fw)) : {FRq.get_plan.width(r, c, _) == goal : Wr.Dec<FRq.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(b, Wr.put_nat(u, s5))), Wr.Got{b, Wr.put_nat(u, s5)}, Wire.wire_nat_round_trip(b, Wr.put_nat(u, s5), fb)) : {FRq.get_plan.budget(r, c, w, _) == goal : Wr.Dec<FRq.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(u, s5)), Wr.Got{u, s5}, Wire.wire_nat_round_trip(u, s5, fu)) : {FRq.get_plan.used(r, c, w, b, _) == goal : Wr.Dec<FRq.Req>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, s5), Wr.Got{ss, rest}, Wire.wire_list_round_trip(ss, rest, fs)) : {FRq.get_plan.sizes(r, c, w, b, u, _) == goal : Wr.Dec<FRq.Req>}
      {==}
    case FRq.QCut{+m, +t}:
      +h0 = h
      +fm = LP.qw.and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(t)), h0)
      +ft = LP.qw.and_r(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(t)), h0)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(m, Wr.put_str(t, rest))), Wr.Got{m, Wr.put_str(t, rest)}, Wire.wire_nat_round_trip(m, Wr.put_str(t, rest), fm)) : {FRq.get_cut(_) == Wr.Got{FRq.QCut{m, t}, rest} : Wr.Dec<FRq.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(t, rest)), Wr.Got{t, rest}, Wire.wire_str_round_trip(t, rest, ft)) : {FRq.get_cut.text(m, _) == Wr.Got{FRq.QCut{m, t}, rest} : Wr.Dec<FRq.Req>}
      {==}

# Replies
# -------

# the model's refusal text is the laws' rq_text
def re.text(f: Rq.Refusal) -> {Rq.text(f) == RlmQuery.rq_text(f) : String}:
  match f:
    case Rq.OverBudget{t, l, b}:
      {==}
    case Rq.Full{c}:
      {==}

def re.plan(p: Rq.Plan) -> {FRq.put_plan(p) == RlmQuery.rq_w_plan(p) : String}:
  match p:
    case Rq.Waves{+ws}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), Wr.put_list(~Nat, ~Wr.put_nat, ws, ""), LawsBase.wire_spell_nats(ws, ""), Wire.wire_nats_spells(ws, ""))
    case Rq.Refused{+f}:
      Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_str(z, "")), Rq.text(f), RlmQuery.rq_text(f), re.text(f))

def re.trim(x: Rq.Trim) -> {FRq.put_trim(x) == RlmQuery.rq_w_trim(x) : String}:
  match x:
    case Rq.Fits{}:
      {==}
    case Rq.CutAt{k}:
      {==}

# the entry's answer is the spec's decision, spelled
def re.reply(q: FRq.Req) -> {FRq.answer(q) == RlmQuery.rq_w_reply(q) : String}:
  match q:
    case FRq.QPlan{+r, +c, +w, +b, +u, +ss}:
      %Equal.sym(Rq.Plan, Rq.plan(r, c, w, b, u, ss), QSpec.plan(r, c, w, b, u, ss), LP.qp.plan(r, c, w, b, u, ss)) : {FRq.put_plan(_) == RlmQuery.rq_w_plan(QSpec.plan(r, c, w, b, u, ss)) : String}
      re.plan(QSpec.plan(r, c, w, b, u, ss))
    case FRq.QCut{+m, +t}:
      +e = Equal.trans(Rq.Trim, Rq.cut(m, t), LC.qc.R(t, m), QSpec.cut(m, t), LC.qc.code(t, m), Equal.sym(Rq.Trim, QSpec.cut(m, t), LC.qc.R(t, m), LC.qc.spec(t, m)))
      %Equal.sym(Rq.Trim, Rq.cut(m, t), QSpec.cut(m, t), e) : {FRq.put_trim(_) == RlmQuery.rq_w_trim(QSpec.cut(m, t)) : String}
      re.trim(QSpec.cut(m, t))

def re.plan_ok(p: Rq.Plan) -> {LawsBase.wire_opens_err(FRq.put_plan(p)) == False{} : Bool}:
  match p:
    case Rq.Waves{ws}:
      {==}
    case Rq.Refused{f}:
      {==}

def re.trim_ok(x: Rq.Trim) -> {LawsBase.wire_opens_err(FRq.put_trim(x)) == False{} : Bool}:
  match x:
    case Rq.Fits{}:
      {==}
    case Rq.CutAt{k}:
      {==}

# no answer opens with 'E'
def re.answer_ok(q: FRq.Req) -> {LawsBase.wire_opens_err(FRq.answer(q)) == False{} : Bool}:
  match q:
    case FRq.QPlan{r, c, w, b, u, ss}:
      re.plan_ok(Rq.plan(r, c, w, b, u, ss))
    case FRq.QCut{m, t}:
      re.trim_ok(Rq.cut(m, t))

# A decoded list of Nats fits
# ---------------------------

def re.GoP(m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {List.length(&2, Nat, xs) == 1n+m : Nat} & {LawsBase.wire_nats_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def re.go.cons(+m: Nat, +x: Nat, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, v: re.GoP(m, d)) -> re.GoP(1n+m, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = v
      (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, xs), 1n+m, e1), LP.qw.and(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(xs), fx, e2))
    case Wr.Bad{}:
      Unit{}

def re.go(m: Nat, +s: String, cur: Wr.Dec<Nat>, ec: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) -> re.GoP(m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m:
    case 0n:
      match cur:
        case Wr.Got{+x, +r}:
          ({==}, LP.qw.and(LawsBase.wire_fits(x), True{}, Wire.wire_nat_decoded_fits(s, x, r, ec), {==}))
        case Wr.Bad{}:
          Unit{}
    case 1n++k:
      match cur:
        case Wr.Got{+x, +r}:
          re.go.cons(k, x, Wire.wire_nat_decoded_fits(s, x, r, ec), Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(r)), re.go(k, r, Wr.get_nat(r), {==}))
        case Wr.Bad{}:
          Unit{}

def re.NF(d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def re.nf.go(+m: Nat, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, v: re.GoP(m, d)) -> re.NF(d):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = v
      %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e1) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
      LP.qw.and(LawsBase.wire_fits(1n+m), LawsBase.wire_nats_fit(xs), fn, e2)
    case Wr.Bad{}:
      Unit{}

def re.nf.n(n: Nat, +s1: String, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> re.NF(Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s1})):
  match n:
    case 0n:
      {==}
    case 1n++m:
      re.nf.go(m, fn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s1)), re.go(m, s1, Wr.get_nat(s1), {==}))

def re.nf.start(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> re.NF(Wr.get_list.start(~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+n, +s1}:
      re.nf.n(n, s1, Wire.wire_nat_decoded_fits(s, n, s1, ed))
    case Wr.Bad{}:
      Unit{}

# a decoded list of Nats fits the wire: its count and every item
def re.nats_fit(+s: String, +xs: List<&2, Nat>, +r: String, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == Wr.Got{xs, r} : Wr.Dec<List<&2, Nat>>}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}:
  %ed : re.NF(_)
  re.nf.start(s, Wr.get_nat(s), {==})

# Decoded requests are spelled
# ----------------------------

def re.RP(s: String, x: Wr.Dec<FRq.Req>) -> Type:
  match x:
    case Wr.Got{q, rr}:
      {s == RlmQuery.rq_w_req(q, rr) : String} & {RlmQuery.rq_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def re.x.sizes(-s: String, +r: Nat, +c: Nat, +w: Nat, +b: Nat, +u: Nat, +s5: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, s5)))))) : String}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fu: {LawsBase.wire_fits(u) == True{} : Bool}, x: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s5) == x : Wr.Dec<List<&2, Nat>>}) -> re.RP(s, FRq.get_plan.sizes(r, c, w, b, u, x)):
  match x:
    case Wr.Got{+ss, +rr}:
      +ee = ed
      +e = Equal.trans(String, s5, Wr.put_list(~Nat, ~Wr.put_nat, ss, rr), LawsBase.wire_spell_nats(ss, rr), Wire.wire_list_exact(s5, ss, rr, ee), Wire.wire_nats_spells(ss, rr))
      +fl = Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ss)), LawsBase.wire_nats_fit(ss))
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, s5)))))), Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, LawsBase.wire_spell_nats(ss, rr))))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, z)))))), s5, LawsBase.wire_spell_nats(ss, rr), e)),
        LP.qw.and(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl)))), fr,
          LP.qw.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl))), fc,
            LP.qw.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl)), fw,
              LP.qw.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), fl), fb,
                LP.qw.and(LawsBase.wire_fits(u), fl, fu, re.nats_fit(s5, ss, rr, ee)))))))
    case Wr.Bad{}:
      Unit{}

def re.x.used(-s: String, +r: Nat, +c: Nat, +w: Nat, +b: Nat, +s4: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, s4))))) : String}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s4) == x : Wr.Dec<Nat>}) -> re.RP(s, FRq.get_plan.used(r, c, w, b, x)):
  match x:
    case Wr.Got{+u, +s5}:
      +e = ed
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, s4))))), Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, s5)))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, z))))), s4, Wr.put_nat(u, s5), Wire.wire_nat_exact(s4, u, s5, e)))
      re.x.sizes(s, r, c, w, b, u, s5, pre2, fr, fc, fw, fb, Wire.wire_nat_decoded_fits(s4, u, s5, e), Wr.get_list(~Nat, ~Wr.get_nat, s5), {==})
    case Wr.Bad{}:
      Unit{}

def re.x.budget(-s: String, +r: Nat, +c: Nat, +w: Nat, +s3: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, s3)))) : String}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == x : Wr.Dec<Nat>}) -> re.RP(s, FRq.get_plan.budget(r, c, w, x)):
  match x:
    case Wr.Got{+b, +s4}:
      +e = ed
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, s3)))), Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, s4))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, z)))), s3, Wr.put_nat(b, s4), Wire.wire_nat_exact(s3, b, s4, e)))
      re.x.used(s, r, c, w, b, s4, pre2, fr, fc, fw, Wire.wire_nat_decoded_fits(s3, b, s4, e), Wr.get_nat(s4), {==})
    case Wr.Bad{}:
      Unit{}

def re.x.width(-s: String, +r: Nat, +c: Nat, +s2: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, s2))) : String}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == x : Wr.Dec<Nat>}) -> re.RP(s, FRq.get_plan.width(r, c, x)):
  match x:
    case Wr.Got{+w, +s3}:
      +e = ed
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, s2))), Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, s3)))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, z))), s2, Wr.put_nat(w, s3), Wire.wire_nat_exact(s2, w, s3, e)))
      re.x.budget(s, r, c, w, s3, pre2, fr, fc, Wire.wire_nat_decoded_fits(s2, w, s3, e), Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def re.x.cap(-s: String, +r: Nat, +s1: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(r, s1)) : String}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == x : Wr.Dec<Nat>}) -> re.RP(s, FRq.get_plan.cap(r, x)):
  match x:
    case Wr.Got{+c, +s2}:
      +e = ed
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(r, s1)), Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, s2))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(r, z)), s1, Wr.put_nat(c, s2), Wire.wire_nat_exact(s1, c, s2, e)))
      re.x.width(s, r, c, s2, pre2, fr, Wire.wire_nat_decoded_fits(s1, c, s2, e), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def re.x.run(-s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == x : Wr.Dec<Nat>}) -> re.RP(s, FRq.get_plan(x)):
  match x:
    case Wr.Got{+r, +s1}:
      +e = ed
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, s0), Wr.put_nat(0n, Wr.put_nat(r, s1)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s0, Wr.put_nat(r, s1), Wire.wire_nat_exact(s0, r, s1, e)))
      re.x.cap(s, r, s1, pre2, Wire.wire_nat_decoded_fits(s0, r, s1, e), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def re.x.text(-s: String, +m: Nat, +s1: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(m, s1)) : String}, fm: {LawsBase.wire_fits(m) == True{} : Bool}, x: Wr.Dec<String>, sp: LE.dcw.SP(s1, x)) -> re.RP(s, FRq.get_cut.text(m, x)):
  match x:
    case Wr.Got{+t, +rr}:
      (e, ft) = sp
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(m, s1)), Wr.put_nat(1n, Wr.put_nat(m, Wr.put_str(t, rr))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(m, z)), s1, Wr.put_str(t, rr), e)), LP.qw.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(t)), fm, ft))
    case Wr.Bad{}:
      Unit{}

def re.x.max(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == x : Wr.Dec<Nat>}) -> re.RP(s, FRq.get_cut(x)):
  match x:
    case Wr.Got{+m, +s1}:
      +e = ed
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, s0), Wr.put_nat(1n, Wr.put_nat(m, s1)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s0, Wr.put_nat(m, s1), Wire.wire_nat_exact(s0, m, s1, e)))
      re.x.text(s, m, s1, pre2, Wire.wire_nat_decoded_fits(s0, m, s1, e), Wr.get_str(s1), LE.dcw.str(s1))
    case Wr.Bad{}:
      Unit{}

def re.x.tag(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> re.RP(s, FRq.get_req.start(x)):
  match x:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          re.x.run(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), Wr.get_nat(s0), {==})
        case 1n:
          re.x.max(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and fits
def re.x.req(+s: String) -> re.RP(s, FRq.get_req(s)):
  re.x.tag(s, Wr.get_nat(s), {==})

def re.T(s: String) -> Type:
  Sigma<&1, &1, FRq.Req, q => {s == RlmQuery.rq_w_req(q, "") : String} & {RlmQuery.rq_fit_req(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def re.top(-s: String, x: Wr.Dec<FRq.Req>, rp: re.RP(s, x), ok: {LawsBase.wire_opens_err(FRq.ffi.got(x)) == False{} : Bool}) -> re.T(s):
  match x:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{y, z}:
          LN.rq.absurd(re.T(s), ok)
    case Wr.Bad{}:
      LN.rq.absurd(re.T(s), ok)

# an answer that opens with 'E' is the one error form
def re.refuse(x: Wr.Dec<FRq.Req>, bad: {LawsBase.wire_opens_err(FRq.ffi.got(x)) == True{} : Bool}) -> {FRq.ffi.got(x) == Wr.err("rlm_query: malformed request") : String}:
  match x:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LN.rq.absurd({FRq.answer(q) == Wr.err("rlm_query: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FRq.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FRq.answer(q)), True{}, bad), re.answer_ok(q)))
        case SCon{y, z}:
          {==}
    case Wr.Bad{}:
      {==}

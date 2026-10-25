# eukhe: the proof of LAW commit_entry_exact
#
# PROOF: each decoder of bend/ffi_doc_commit.bend answers Got{x, rest}
# only for an input that is the spec's spelling of x before rest, with x
# within the wire (a predicate per decoder answer, carried stage by stage
# with wire_nat_exact, wire_bool_exact, wire_str_exact, a too long count
# refused by wire_nat_too_long, and one exactness lemma per list item:
# Met, Fate, String, Ent). The entry answers a value only for a request
# read whole with nothing left: that input is the spelled request.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../bend/ffi_doc_commit.bend as FCm
import ../../bend/wire.bend as Wr
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./base.bend as LA
import ../base/wire_dec.bend as LE
import ./entry/list_met.bend as LM
import ./entry/list_fate.bend as LFa
import ../base/wire_strs.bend as LS
import ./entry/list_ents.bend as LN
import ./entry/fields.bend as LF

def dcw.RP(s: String, d: Wr.Dec<FCm.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == DocCommit.sp_w_req(q, r) : String} & {DocCommit.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dcw.req.check(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<List<&2, Cm.Met>>, ls: LM.dcw.mets.LS(s1, d)) -> dcw.RP(s, FCm.get_check(d)):
  match d:
    case Wr.Got{+ms, +r}:
      (e, f) = ls
      (LE.dcw.after(s, 0n, s1, Wr.put_list(~Cm.Met, ~DocCommit.sp_w_met, ms, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def dcw.req.publish(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Cm.Pub>, pp: LF.dcw.PbP(s1, d)) -> dcw.RP(s, FCm.get_publish(d)):
  match d:
    case Wr.Got{+p, +r}:
      (LE.dcw.after(s, 1n, s1, DocCommit.sp_w_pub(p, r), pre, pp), {==})
    case Wr.Bad{}:
      Unit{}

def dcw.req.answer(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<List<&2, Cm.Fate>>, ls: LFa.dcw.fates.LS(s1, d)) -> dcw.RP(s, FCm.get_answer(d)):
  match d:
    case Wr.Got{+fs, +r}:
      (e, f) = ls
      (LE.dcw.after(s, 2n, s1, Wr.put_list(~Cm.Fate, ~DocCommit.sp_w_fate, fs, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def dcw.req.gdisk(-s: String, +b: Cm.Base, -s2: String, pre: {s == Wr.put_nat(3n, DocCommit.sp_w_base(b, s2)) : String}, fb: {DocCommit.sp_fit_base(b) == True{} : Bool}, d: Wr.Dec<Cm.Disk>, dp: LF.dcw.DP(s2, d)) -> dcw.RP(s, FCm.get_gate.disk(b, d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = dp
      (Equal.trans(String, s, Wr.put_nat(3n, DocCommit.sp_w_base(b, s2)), Wr.put_nat(3n, DocCommit.sp_w_base(b, DocCommit.sp_w_disk(x, r))), pre, Equal.cong(String, String, z => Wr.put_nat(3n, DocCommit.sp_w_base(b, z)), s2, DocCommit.sp_w_disk(x, r), e)), LA.dcw.and_tt(DocCommit.sp_fit_base(b), DocCommit.sp_fit_disk(x), fb, f))
    case Wr.Bad{}:
      Unit{}

def dcw.req.gate(-s: String, -s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Cm.Base>, bp: LF.dcw.BP(s1, d)) -> dcw.RP(s, FCm.get_gate(d)):
  match d:
    case Wr.Got{+b, +s2}:
      (e, f) = bp
      dcw.req.gdisk(s, b, s2, LE.dcw.after(s, 3n, s1, DocCommit.sp_w_base(b, s2), pre, e), f, FCm.get_disk(Wr.get_nat(s2)), LF.dcw.disk(s2))
    case Wr.Bad{}:
      Unit{}

def dcw.req.slist(-s: String, +dg: String, -s2: String, pre: {s == Wr.put_nat(4n, Wr.put_str(dg, s2)) : String}, fd: {LawsBase.wire_fits(String.length(dg)) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, ls: LS.dcw.strs.LS(s2, d)) -> dcw.RP(s, FCm.get_seen.list(dg, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e, fg) = ls
      (f, g) = fg
      (Equal.trans(String, s, Wr.put_nat(4n, Wr.put_str(dg, s2)), Wr.put_nat(4n, Wr.put_str(dg, Wr.put_list(~String, ~Wr.put_str, xs, r))), pre, Equal.cong(String, String, z => Wr.put_nat(4n, Wr.put_str(dg, z)), s2, Wr.put_list(~String, ~Wr.put_str, xs, r), e)),
        LA.dcw.and_tt(LawsBase.wire_fits(String.length(dg)), Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), DocCommit.sp_fit_strs(xs)), fd, LA.dcw.and_tt(LawsBase.wire_fits(List.length(&2, String, xs)), DocCommit.sp_fit_strs(xs), f, g)))
    case Wr.Bad{}:
      Unit{}

def dcw.req.seen(-s: String, -s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> dcw.RP(s, FCm.get_seen(d)):
  match d:
    case Wr.Got{+dg, +s2}:
      (e, f) = sp
      dcw.req.slist(s, dg, s2, LE.dcw.after(s, 4n, s1, Wr.put_str(dg, s2), pre, e), f, FCm.get_strs(s2), LS.dcw.strs.list(s2))
    case Wr.Bad{}:
      Unit{}

def dcw.req.prefix(-s: String, -s1: String, pre: {s == Wr.put_nat(5n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> dcw.RP(s, FCm.get_prefix(d)):
  match d:
    case Wr.Got{+h, +r}:
      (e, f) = sp
      (LE.dcw.after(s, 5n, s1, Wr.put_str(h, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def dcw.req.sents(-s: String, +h: String, -s2: String, pre: {s == Wr.put_nat(6n, Wr.put_str(h, s2)) : String}, fh: {LawsBase.wire_fits(String.length(h)) == True{} : Bool}, d: Wr.Dec<List<&2, Cm.Ent>>, ls: LN.dcw.ents.LS(s2, d)) -> dcw.RP(s, FCm.get_sweep.ents(h, d)):
  match d:
    case Wr.Got{+es, +r}:
      (e, fg) = ls
      (f, g) = fg
      (Equal.trans(String, s, Wr.put_nat(6n, Wr.put_str(h, s2)), Wr.put_nat(6n, Wr.put_str(h, Wr.put_list(~Cm.Ent, ~DocCommit.sp_w_ent, es, r))), pre, Equal.cong(String, String, z => Wr.put_nat(6n, Wr.put_str(h, z)), s2, Wr.put_list(~Cm.Ent, ~DocCommit.sp_w_ent, es, r), e)),
        LA.dcw.and_tt(LawsBase.wire_fits(String.length(h)), Bool.and(LawsBase.wire_fits(List.length(&2, Cm.Ent, es)), DocCommit.sp_fit_ents(es)), fh, LA.dcw.and_tt(LawsBase.wire_fits(List.length(&2, Cm.Ent, es)), DocCommit.sp_fit_ents(es), f, g)))
    case Wr.Bad{}:
      Unit{}

def dcw.req.sweep(-s: String, -s1: String, pre: {s == Wr.put_nat(6n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> dcw.RP(s, FCm.get_sweep(d)):
  match d:
    case Wr.Got{+h, +s2}:
      (e, f) = sp
      dcw.req.sents(s, h, s2, LE.dcw.after(s, 6n, s1, Wr.put_str(h, s2), pre, e), f, Wr.get_list(~Cm.Ent, ~FCm.get_ent, s2), LN.dcw.ents.list(s2))
    case Wr.Bad{}:
      Unit{}

def dcw.req.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dcw.RP(s, FCm.get_req.tag(t, s1)):
  match t:
    case 0n:
      dcw.req.check(s, s1, pre, Wr.get_list(~Cm.Met, ~FCm.get_met, s1), LM.dcw.mets.list(s1))
    case 1n:
      dcw.req.publish(s, s1, pre, FCm.get_pub(Wr.get_nat(s1)), LF.dcw.pub(s1))
    case 2n:
      dcw.req.answer(s, s1, pre, Wr.get_list(~Cm.Fate, ~FCm.get_fate, s1), LFa.dcw.fates.list(s1))
    case 3n:
      dcw.req.gate(s, s1, pre, FCm.get_base(Wr.get_nat(s1)), LF.dcw.base(s1))
    case 4n:
      dcw.req.seen(s, s1, pre, Wr.get_str(s1), LE.dcw.str(s1))
    case 5n:
      dcw.req.prefix(s, s1, pre, Wr.get_str(s1), LE.dcw.str(s1))
    case 6n:
      dcw.req.sweep(s, s1, pre, Wr.get_str(s1), LE.dcw.str(s1))
    case 7n+u:
      Unit{}

def dcw.req.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> dcw.RP(s, FCm.get_req.start(d)):
  match d:
    case Wr.Got{t, s1}:
      dcw.req.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and fits the wire
def dcw.req(+s: String) -> dcw.RP(s, FCm.get_req(s)):
  dcw.req.go(s, Wr.get_nat(s), LE.dcw.nat(s))

# a value answered: a request read whole, nothing left
def dcw.top(-s: String, d: Wr.Dec<FCm.Req>, rp: dcw.RP(s, d), ok: {LawsBase.wire_opens_err(FCm.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FCm.Req, r => {s == DocCommit.sp_w_req(r, "") : String} & {DocCommit.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LA.dcw.tf(Sigma<&1, &1, FCm.Req, r2 => {s == DocCommit.sp_w_req(r2, "") : String} & {DocCommit.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LA.dcw.tf(Sigma<&1, &1, FCm.Req, r2 => {s == DocCommit.sp_w_req(r2, "") : String} & {DocCommit.sp_fit_req(r2) == True{} : Bool}>, ok)

def DocCommit.commit_entry_exact(s, ok):
  dcw.top(s, FCm.get_req(s), dcw.req(s), ok)

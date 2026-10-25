# eukhe: the proof of LAW slash_suggest_entry_exact
#
# PROOF: each decoder of bend/ffi_slash_suggest.bend answers Got{x, rest}
# only for an input that is the spec's spelling of x before rest, with x
# within the wire (ssx.*: a predicate per decoder answer, carried stage by
# stage with the shared string and list exactness lemmas: dcw.str,
# dcw.strs.list). The entry answers a value only for a request read whole
# with nothing left: that input is the spelled request (ssx.top).

import Base
import ../../bend/slash_suggest.bend as Ss
import ../../bend/ffi_slash_suggest.bend as FSs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/slash_suggest.bend as SlashSuggest
import ../../laws/doc_commit.bend as DocCommit
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../base/wire_dec.bend as LE
import ../base/wire_strs.bend as LS
import ./base.bend as LA

def ssx.RP(s: String, d: Wr.Dec<FSs.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == SlashSuggest.sp_w_req(q, r) : String} & {SlashSuggest.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ssx.names(-s: String, +w: String, -s2: String, pre: {s == Wr.put_str(w, s2) : String}, fw: {LawsBase.wire_fits(String.length(w)) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, ls: LS.dcw.strs.LS(s2, d)) -> ssx.RP(s, FSs.get_req.names(w, d)):
  match d:
    case Wr.Got{+cs, +r}:
      (e, fs2) = ls
      (fn, fd) = fs2
      +fa = Equal.trans(Bool, SlashSuggest.sp_fit_strs(cs), DocCommit.sp_fit_strs(cs), True{}, LA.ssb.fits(cs), fd)
      (Equal.trans(String, s, Wr.put_str(w, s2), Wr.put_str(w, Wr.put_list(~String, ~Wr.put_str, cs, r)), pre, Equal.cong(String, String, z => Wr.put_str(w, z), s2, Wr.put_list(~String, ~Wr.put_str, cs, r), e)),
        LBool.cb_and_intro(LawsBase.wire_fits(String.length(w)), Bool.and(LawsBase.wire_fits(List.length(&2, String, cs)), SlashSuggest.sp_fit_strs(cs)), fw, LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, String, cs)), SlashSuggest.sp_fit_strs(cs), fn, fa)))
    case Wr.Bad{}:
      Unit{}

def ssx.typed(+s: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s, d)) -> ssx.RP(s, FSs.get_req.typed(d)):
  match d:
    case Wr.Got{+w, +s2}:
      (e, fw) = sp
      ssx.names(s, w, s2, e, fw, Wr.get_list(~String, ~Wr.get_str, s2), LS.dcw.strs.list(s2))
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def ssx.top(-s: String, d: Wr.Dec<FSs.Req>, rp: ssx.RP(s, d), ok: {LawsBase.wire_opens_err(FSs.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FSs.Req, r => {s == SlashSuggest.sp_w_req(r, "") : String} & {SlashSuggest.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FSs.Req, r2 => {s == SlashSuggest.sp_w_req(r2, "") : String} & {SlashSuggest.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FSs.Req, r2 => {s == SlashSuggest.sp_w_req(r2, "") : String} & {SlashSuggest.sp_fit_req(r2) == True{} : Bool}>, ok)

def SlashSuggest.slash_suggest_entry_exact(s, ok):
  ssx.top(s, FSs.get_req(s), ssx.typed(s, Wr.get_str(s), LE.dcw.str(s)), ok)

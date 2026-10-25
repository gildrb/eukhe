# eukhe: the proof of LAW dash_access_entry_exact
#
# PROOF: each decoder of bend/ffi_dash_access.bend answers Got{x, rest}
# only for an input that is the spec's spelling of x before rest, with x
# within the wire (dax.*: a predicate per decoder answer, carried stage by
# stage with the string, Nat and list exactness lemmas of the doc_commit
# entry: dcw.nat, dcw.str, dcw.strs.list). The entry answers a value only
# for a request read whole with nothing left: that input is the spelled
# request (dax.top).

import Base
import ../../bend/ffi_dash_access.bend as FAc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash_access.bend as DashAccess
import ../../laws/doc_commit.bend as DocCommit
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../base/wire_dec.bend as LE
import ../base/wire_strs.bend as LS
import ./base.bend as LA

def dax.RP(s: String, d: Wr.Dec<FAc.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == DashAccess.sp_w_req(q, r) : String} & {DashAccess.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dax.host.allowed(-s: String, +hh: String, -s2: String, pre: {s == Wr.put_nat(0n, Wr.put_str(hh, s2)) : String}, fh: {LawsBase.wire_fits(String.length(hh)) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, ls: LS.dcw.strs.LS(s2, d)) -> dax.RP(s, FAc.get_host.allowed(hh, d)):
  match d:
    case Wr.Got{+al, +r}:
      (e, fs2) = ls
      (fn, fd) = fs2
      +fa = Equal.trans(Bool, DashAccess.sp_fit_strs(al), DocCommit.sp_fit_strs(al), True{}, LA.dab.fits(al), fd)
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_str(hh, s2)), Wr.put_nat(0n, Wr.put_str(hh, Wr.put_list(~String, ~Wr.put_str, al, r))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_str(hh, z)), s2, Wr.put_list(~String, ~Wr.put_str, al, r), e)),
        LBool.cb_and_intro(LawsBase.wire_fits(String.length(hh)), Bool.and(LawsBase.wire_fits(List.length(&2, String, al)), DashAccess.sp_fit_strs(al)), fh, LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, String, al)), DashAccess.sp_fit_strs(al), fn, fa)))
    case Wr.Bad{}:
      Unit{}

def dax.host(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> dax.RP(s, FAc.get_host(d)):
  match d:
    case Wr.Got{+hh, +s2}:
      (e, fh) = sp
      dax.host.allowed(s, hh, s2, Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_str(hh, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_str(hh, s2), e)), fh, Wr.get_list(~String, ~Wr.get_str, s2), LS.dcw.strs.list(s2))
    case Wr.Bad{}:
      Unit{}

def dax.origin.host(-s: String, +o: String, -s2: String, pre: {s == Wr.put_nat(1n, Wr.put_str(o, s2)) : String}, fo: {LawsBase.wire_fits(String.length(o)) == True{} : Bool}, d: Wr.Dec<String>, sp: LE.dcw.SP(s2, d)) -> dax.RP(s, FAc.get_origin.host(o, d)):
  match d:
    case Wr.Got{+hh, +r}:
      (e, fh) = sp
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_str(o, s2)), Wr.put_nat(1n, Wr.put_str(o, Wr.put_str(hh, r))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_str(o, z)), s2, Wr.put_str(hh, r), e)),
        LBool.cb_and_intro(LawsBase.wire_fits(String.length(o)), LawsBase.wire_fits(String.length(hh)), fo, fh))
    case Wr.Bad{}:
      Unit{}

def dax.origin(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> dax.RP(s, FAc.get_origin(d)):
  match d:
    case Wr.Got{+o, +s2}:
      (e, fo) = sp
      dax.origin.host(s, o, s2, Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(o, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_str(o, s2), e)), fo, Wr.get_str(s2), LE.dcw.str(s2))
    case Wr.Bad{}:
      Unit{}

def dax.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dax.RP(s, FAc.get_req.tag(t, s1)):
  match t:
    case 0n:
      dax.host(s, s1, pre, Wr.get_str(s1), LE.dcw.str(s1))
    case 1n:
      dax.origin(s, s1, pre, Wr.get_str(s1), LE.dcw.str(s1))
    case 2n+u:
      Unit{}

def dax.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> dax.RP(s, FAc.get_req.start(d)):
  match d:
    case Wr.Got{t, s1}:
      dax.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def dax.top(-s: String, d: Wr.Dec<FAc.Req>, rp: dax.RP(s, d), ok: {LawsBase.wire_opens_err(FAc.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FAc.Req, r => {s == DashAccess.sp_w_req(r, "") : String} & {DashAccess.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FAc.Req, r2 => {s == DashAccess.sp_w_req(r2, "") : String} & {DashAccess.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FAc.Req, r2 => {s == DashAccess.sp_w_req(r2, "") : String} & {DashAccess.sp_fit_req(r2) == True{} : Bool}>, ok)

def DashAccess.dash_access_entry_exact(s, ok):
  dax.top(s, FAc.get_req(s), dax.go(s, Wr.get_nat(s), LE.dcw.nat(s)), ok)

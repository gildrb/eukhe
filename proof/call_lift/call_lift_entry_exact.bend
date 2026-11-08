# eukhe: the proof of LAW call_lift_entry_exact
#
# PROOF: the entry reads a request as the laws' reader (cle.req), whose
# list reader is LawsBase.wire_read_list (wire_list_reads_items): the
# count, then exactly that many calls. Each stage answers Got{x, rest}
# only for an input that is the spec's spelling of x before rest, with
# every count and length within the wire (clx.*: a predicate per decoder
# answer, carried stage by stage with wire_str_exact, wire_strs_exact,
# wire_nat_exact and their decoded_fits laws). The entry answers a value
# only for a request read whole with nothing left: that input is the
# spelled request (clx.top).

import Base
import ../../bend/call_lift.bend as Cl
import ../../bend/ffi_call_lift.bend as FCl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/call_lift.bend as CallLift
import ../../spec/harness/lift_wire.bend as SpW
import ../wire/wire_list_reads_items.bend as PWireListReadsItems
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../wire/wire_strs_exact.bend as PWireStrsExact
import ../wire/wire_strs_decoded_fit.bend as PWireStrsDecodedFit
import ../wire/wire_strs_spells.bend as PWireStrsSpells
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ./base/read.bend as LCallLiftRead

# Calls
# -----

# what a call reader's answer says about its input s
def clx.CP(s: String, d: Wr.Dec<Cl.Call>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == SpW.w_call(c, r) : String} & {SpW.fit_call(c) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def clx.keys(-s: String, +f: String, +r: String, +s2: String, e: {s == Wr.put_str(f, Wr.put_str(r, s2)) : String}, ff: {LawsBase.wire_fits(String.length(f)) == True{} : Bool}, fr: {LawsBase.wire_fits(String.length(r)) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s2) == d : Wr.Dec<List<&2, String>>}) -> clx.CP(s, SpW.r_call.keys(f, r, d)):
  match d:
    case Wr.Got{+ks, +rest}:
      +e2 = ed
      +ek = Equal.trans(String, s2, LawsBase.wire_spell_strs(ks, rest), Wr.put_list(~String, ~Wr.put_str, ks, rest), Wire.wire_strs_exact(s2, ks, rest, e2), Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, ks, rest), LawsBase.wire_spell_strs(ks, rest), Wire.wire_strs_spells(ks, rest)))
      +fk = Wire.wire_strs_decoded_fit(s2, ks, rest, e2)
      (Equal.trans(String, s, Wr.put_str(f, Wr.put_str(r, s2)), Wr.put_str(f, Wr.put_str(r, Wr.put_list(~String, ~Wr.put_str, ks, rest))), e, Equal.cong(String, String, z => Wr.put_str(f, Wr.put_str(r, z)), s2, Wr.put_list(~String, ~Wr.put_str, ks, rest), ek)), LBool.cb_and_intro(LawsBase.wire_fits(String.length(f)), Bool.and(LawsBase.wire_fits(String.length(r)), LawsBase.wire_strs_fit(ks)), ff, LBool.cb_and_intro(LawsBase.wire_fits(String.length(r)), LawsBase.wire_strs_fit(ks), fr, fk)))
    case Wr.Bad{}:
      Unit{}

def clx.rev(-s: String, +f: String, +s1: String, ef: {s == Wr.put_str(f, s1) : String}, ff: {LawsBase.wire_fits(String.length(f)) == True{} : Bool}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> clx.CP(s, SpW.r_call.rev(f, d)):
  match d:
    case Wr.Got{+r, +s2}:
      +e2 = ed
      +e = Equal.trans(String, s, Wr.put_str(f, s1), Wr.put_str(f, Wr.put_str(r, s2)), ef, Equal.cong(String, String, z => Wr.put_str(f, z), s1, Wr.put_str(r, s2), Wire.wire_str_exact(s1, r, s2, e2)))
      clx.keys(s, f, r, s2, e, ff, Wire.wire_str_decoded_fits(s1, r, s2, e2), Wr.get_list(~String, ~Wr.get_str, s2), {==})
    case Wr.Bad{}:
      Unit{}

def clx.fam(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> clx.CP(s, SpW.r_call.fam(d)):
  match d:
    case Wr.Got{+f, +s1}:
      +e = ed
      clx.rev(s, f, s1, Wire.wire_str_exact(s, f, s1, e), Wire.wire_str_decoded_fits(s, f, s1, e), Wr.get_str(s1), {==})
    case Wr.Bad{}:
      Unit{}

# the call reader accepts only spelled calls that fit
def clx.call(+s: String) -> clx.CP(s, SpW.r_call(s)):
  clx.fam(s, Wr.get_str(s), {==})

def clx.call_at(+s: String, -d: Wr.Dec<Cl.Call>, ed: {SpW.r_call(s) == d : Wr.Dec<Cl.Call>}) -> clx.CP(s, d):
  %ed : clx.CP(s, _)
  clx.call(s)

# The calls
# ---------

# what the item reader's answer says about its input s (n calls)
def clx.IP(s: String, n: Nat, d: Wr.Dec<List<&2, Cl.Call>>) -> Type:
  match d:
    case Wr.Got{cs, r}:
      {s == SpW.w_calls(cs, r) : String} & ({List.length(&2, Cl.Call, cs) == n : Nat} & {SpW.fit_calls(cs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

# a call before calls read
def clx.cons(-s: String, +c: Cl.Call, +r1: String, -n: Nat, d: Wr.Dec<List<&2, Cl.Call>>, ih: clx.IP(r1, n, d), cp: {s == SpW.w_call(c, r1) : String} & {SpW.fit_call(c) == True{} : Bool}) -> clx.IP(s, 1n+n, LawsBase.wire_items.cons(Cl.Call, c, d)):
  match d:
    case Wr.Got{+cs, +r}:
      (e1, (e2, e3)) = ih
      (ec, fc) = cp
      (Equal.trans(String, s, SpW.w_call(c, r1), SpW.w_call(c, SpW.w_calls(cs, r)), ec, Equal.cong(String, String, z => SpW.w_call(c, z), r1, SpW.w_calls(cs, r), e1)), (Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Cl.Call, cs), n, e2), LBool.cb_and_intro(SpW.fit_call(c), SpW.fit_calls(cs), fc, e3)))
    case Wr.Bad{}:
      Unit{}

# m + 1 calls, the first read from s as cur
def clx.items(m: Nat, cur: Wr.Dec<Cl.Call>, +s: String, er: {SpW.r_call(s) == cur : Wr.Dec<Cl.Call>}) -> clx.IP(s, 1n+m, LawsBase.wire_items.then(Cl.Call, cur, r => LawsBase.wire_items(~Cl.Call, ~SpW.r_call, m, r))):
  match m cur:
    case 0n Wr.Got{+c, +r1}:
      clx.cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, ({==}, {==})), clx.call_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      clx.cons(s, c, r1, 1n+k, LawsBase.wire_items.then(Cl.Call, SpW.r_call(r1), r => LawsBase.wire_items(~Cl.Call, ~SpW.r_call, k, r)), clx.items(k, SpW.r_call(r1), r1, {==}), clx.call_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def clx.items_of(n: Nat, +s: String) -> clx.IP(s, n, LawsBase.wire_items(~Cl.Call, ~SpW.r_call, n, s)):
  match n:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+m:
      clx.items(m, SpW.r_call(s), s, {==})

# The request
# -----------

# what the request reader's answer says about its input s
def clx.RP(s: String, d: Wr.Dec<List<&2, Cl.Call>>) -> Type:
  match d:
    case Wr.Got{cs, r}:
      {s == SpW.w_req(cs, r) : String} & {SpW.fit_req(cs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def clx.list(-s: String, +n: Nat, +s1: String, en: {s == Wr.put_nat(n, s1) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<List<&2, Cl.Call>>, ip: clx.IP(s1, n, d)) -> clx.RP(s, d):
  match d:
    case Wr.Got{+cs, +r}:
      (e1, (e2, e3)) = ip
      +ln = e2
      +w = SpW.w_calls(cs, r)
      +es = Equal.trans(String, s, Wr.put_nat(n, s1), Wr.put_nat(n, w), en, Equal.cong(String, String, z => Wr.put_nat(n, z), s1, w, e1))
      +el = Equal.cong(Nat, String, k => Wr.put_nat(k, w), n, List.length(&2, Cl.Call, cs), Equal.sym(Nat, List.length(&2, Cl.Call, cs), n, ln))
      +fl = Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Cl.Call, cs)), LawsBase.wire_fits(n), True{}, Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, Cl.Call, cs), n, ln), fn)
      (Equal.trans(String, s, Wr.put_nat(n, w), Wr.put_nat(List.length(&2, Cl.Call, cs), w), es, el), LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, Cl.Call, cs)), SpW.fit_calls(cs), fl, e3))
    case Wr.Bad{}:
      Unit{}

def clx.count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> clx.RP(s, LawsBase.wire_read_list.count(~Cl.Call, ~SpW.r_call, d)):
  match d:
    case Wr.Got{+n, +s1}:
      +e = ed
      clx.list(s, n, s1, Wire.wire_nat_exact(s, n, s1, e), Wire.wire_nat_decoded_fits(s, n, s1, e), LawsBase.wire_items(~Cl.Call, ~SpW.r_call, n, s1), clx.items_of(n, s1))
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def clx.top(-s: String, d: Wr.Dec<List<&2, Cl.Call>>, rp: clx.RP(s, d), ok: {LawsBase.wire_opens_err(FCl.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, List<&2, Cl.Call>, cs => {s == SpW.w_req(cs, "") : String} & {SpW.fit_req(cs) == True{} : Bool}>:
  match d:
    case Wr.Got{+cs, rest}:
      match rest:
        case SNil{}:
          (cs, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, List<&2, Cl.Call>, c2 => {s == SpW.w_req(c2, "") : String} & {SpW.fit_req(c2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, List<&2, Cl.Call>, c2 => {s == SpW.w_req(c2, "") : String} & {SpW.fit_req(c2) == True{} : Bool}>, ok)

def CallLift.call_lift_entry_exact(s, ok):
  +rd = LawsBase.wire_read_list(~Cl.Call, ~SpW.r_call, s)
  +e = Equal.trans(Wr.Dec<List<&2, Cl.Call>>, FCl.get_req(s), Wr.get_list(~Cl.Call, ~SpW.r_call, s), rd, LCallLiftRead.cle.req(s), Wire.wire_list_reads_items(~Cl.Call, ~SpW.r_call, s))
  +ok2 = Equal.trans(Bool, LawsBase.wire_opens_err(FCl.ffi.got(rd)), LawsBase.wire_opens_err(FCl.ffi.got(FCl.get_req(s))), False{}, Equal.cong(Wr.Dec<List<&2, Cl.Call>>, Bool, z => LawsBase.wire_opens_err(FCl.ffi.got(z)), rd, FCl.get_req(s), Equal.sym(Wr.Dec<List<&2, Cl.Call>>, FCl.get_req(s), rd, e)), ok)
  clx.top(s, rd, clx.count(s, Wr.get_nat(s), {==}), ok2)

# eukhe: the proof of LAW work_list_entry_exact
#
# PROOF: the decoder answers Got{done, rest} only for an input that is the
# list encoding of done before rest (LLog.pe.bools_exact), which is the
# spec's spelling (LA.wlb.put_list), with the count within the wire (a
# count past it makes the list decoder refuse: wlx.count_fits). The entry
# answers a value only for a request read whole with nothing left: that
# input is the spelled request (wlx.top).

import Base
import ../../bend/ffi_work_list.bend as FWl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/work_list.bend as WorkList
import ../wire/wire_nat_too_long.bend as PWireNatTooLong
import ../base/staging.bend as LStg
import ../base/wire_dec.bend as LE
import ../log/base.bend as LLog
import ./base.bend as LA

def wlx.RP(s: String, d: Wr.Dec<List<&2, Bool>>) -> Type:
  match d:
    case Wr.Got{done, r}:
      {s == WorkList.sp_w_req(done, r) : String} & {WorkList.sp_fit_req(done) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a list decoded from a count past the wire is refused
def wlx.count_fits(b: Bool, +n: Nat, +x: String, -ks: List<&2, Bool>, -r: String, eb: {LawsBase.wire_fits(n) == b : Bool}, ed: {Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, x)) == Wr.Got{ks, r} : Wr.Dec<List<&2, Bool>>}) -> {LawsBase.wire_fits(n) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +c = Equal.trans(Wr.Dec<List<&2, Bool>>, Wr.Got{ks, r}, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, x)), Wr.Bad{}, Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, x)), Wr.Got{ks, r}, ed), Equal.cong(Wr.Dec<Nat>, Wr.Dec<List<&2, Bool>>, z => Wr.get_list.start(~Bool, ~Wr.get_bool, z), Wr.get_nat(Wr.put_nat(n, x)), Wr.Bad{}, Wire.wire_nat_too_long(n, x, eb)))
      LE.dcw.got_bad(List<&2, Bool>, {LawsBase.wire_fits(n) == True{} : Bool}, ks, r, c)

def wlx.items(+s: String, d: Wr.Dec<List<&2, Bool>>, ed: {Wr.get_list(~Bool, ~Wr.get_bool, s) == d : Wr.Dec<List<&2, Bool>>}) -> wlx.RP(s, d):
  match d:
    case Wr.Got{+ks, +r}:
      +e2 = ed
      +sp = Wr.put_nat(List.length(&2, Bool, ks), WorkList.sp_w_bools(ks, r))
      +ex = Equal.trans(String, s, Wr.put_list(~Bool, ~Wr.put_bool, ks, r), sp, LLog.pe.bools_exact(s, ks, r, e2), LA.wlb.put_list(ks, r))
      +ed2 = Equal.trans(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, sp), Wr.get_list(~Bool, ~Wr.get_bool, s), Wr.Got{ks, r}, Equal.cong(String, Wr.Dec<List<&2, Bool>>, z => Wr.get_list(~Bool, ~Wr.get_bool, z), sp, s, Equal.sym(String, s, sp, ex)), e2)
      +fn = wlx.count_fits(LawsBase.wire_fits(List.length(&2, Bool, ks)), List.length(&2, Bool, ks), WorkList.sp_w_bools(ks, r), ks, r, {==}, ed2)
      (ex, fn)
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def wlx.top(-s: String, d: Wr.Dec<List<&2, Bool>>, rp: wlx.RP(s, d), ok: {LawsBase.wire_opens_err(FWl.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, List<&2, Bool>, r => {s == WorkList.sp_w_req(r, "") : String} & {WorkList.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, List<&2, Bool>, r2 => {s == WorkList.sp_w_req(r2, "") : String} & {WorkList.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, List<&2, Bool>, r2 => {s == WorkList.sp_w_req(r2, "") : String} & {WorkList.sp_fit_req(r2) == True{} : Bool}>, ok)

def WorkList.work_list_entry_exact(s, ok):
  wlx.top(s, FWl.get_req(s), wlx.items(s, Wr.get_list(~Bool, ~Wr.get_bool, s), {==}), ok)

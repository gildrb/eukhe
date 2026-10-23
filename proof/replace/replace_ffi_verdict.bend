# eukhe: the proof of LAW replace_ffi_verdict

import Base
import ../../bend/ffi_replace.bend as FRp
import ../../bend/replace.bend as Rp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/replace.bend as Replace
import ../../laws/wire.bend as Wire
import ../base.bend as L
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

def fr.caller_rt(k: Rp.Caller) -> {FRp.get_caller(FRp.put_caller(k, "")) == Wr.Got{k, ""} : Wr.Dec<Rp.Caller>}:
  match k:
    case Rp.Interactive{}:
      {==}
    case Rp.Background{}:
      {==}

# a Verdict request reads back
def fr.rt_verdict(+c: String, +d: String, +same: Bool, +k: Rp.Caller, hc: {LawsBase.wire_fits(String.length(c)) == True{} : Bool}, hd: {LawsBase.wire_fits(String.length(d)) == True{} : Bool}) -> {FRp.get_req(FRp.put_req(FRp.ReqVerdict{c, d, same, k}, "")) == Wr.Got{FRp.ReqVerdict{c, d, same, k}, ""} : Wr.Dec<FRp.Req>}:
  Equal.trans(Wr.Dec<FRp.Req>, FRp.get_req(FRp.put_req(FRp.ReqVerdict{c, d, same, k}, "")), FRp.get_req.of(Wr.Got{1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, FRp.put_caller(k, ""))))}), Wr.Got{FRp.ReqVerdict{c, d, same, k}, ""}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<FRp.Req>, zq => FRp.get_req.of(zq), Wr.get_nat(Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, FRp.put_caller(k, "")))))), Wr.Got{1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, FRp.put_caller(k, ""))))}, Wire.wire_nat_round_trip(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, FRp.put_caller(k, "")))), {==})), Equal.trans(Wr.Dec<FRp.Req>, FRp.get_req.of(Wr.Got{1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, FRp.put_caller(k, ""))))}), FRp.get_verdict(Wr.Got{c, Wr.put_str(d, Wr.put_bool(same, FRp.put_caller(k, "")))}), Wr.Got{FRp.ReqVerdict{c, d, same, k}, ""}, Equal.cong(Wr.Dec<String>, Wr.Dec<FRp.Req>, zq => FRp.get_verdict(zq), Wr.get_str(Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, FRp.put_caller(k, ""))))), Wr.Got{c, Wr.put_str(d, Wr.put_bool(same, FRp.put_caller(k, "")))}, Wire.wire_str_round_trip(c, Wr.put_str(d, Wr.put_bool(same, FRp.put_caller(k, ""))), hc)), Equal.trans(Wr.Dec<FRp.Req>, FRp.get_verdict(Wr.Got{c, Wr.put_str(d, Wr.put_bool(same, FRp.put_caller(k, "")))}), FRp.get_verdict.d(c, Wr.Got{d, Wr.put_bool(same, FRp.put_caller(k, ""))}), Wr.Got{FRp.ReqVerdict{c, d, same, k}, ""}, Equal.cong(Wr.Dec<String>, Wr.Dec<FRp.Req>, zq => FRp.get_verdict.d(c, zq), Wr.get_str(Wr.put_str(d, Wr.put_bool(same, FRp.put_caller(k, "")))), Wr.Got{d, Wr.put_bool(same, FRp.put_caller(k, ""))}, Wire.wire_str_round_trip(d, Wr.put_bool(same, FRp.put_caller(k, "")), hd)), Equal.trans(Wr.Dec<FRp.Req>, FRp.get_verdict.d(c, Wr.Got{d, Wr.put_bool(same, FRp.put_caller(k, ""))}), FRp.get_verdict.same(c, d, Wr.Got{same, FRp.put_caller(k, "")}), Wr.Got{FRp.ReqVerdict{c, d, same, k}, ""}, Equal.cong(Wr.Dec<Bool>, Wr.Dec<FRp.Req>, zq => FRp.get_verdict.same(c, d, zq), Wr.get_bool(Wr.put_bool(same, FRp.put_caller(k, ""))), Wr.Got{same, FRp.put_caller(k, "")}, Wire.wire_bool_round_trip(same, FRp.put_caller(k, ""))), Equal.trans(Wr.Dec<FRp.Req>, FRp.get_verdict.same(c, d, Wr.Got{same, FRp.put_caller(k, "")}), FRp.get_verdict.k(c, d, same, Wr.Got{k, ""}), Wr.Got{FRp.ReqVerdict{c, d, same, k}, ""}, Equal.cong(Wr.Dec<Rp.Caller>, Wr.Dec<FRp.Req>, zq => FRp.get_verdict.k(c, d, same, zq), FRp.get_caller(FRp.put_caller(k, "")), Wr.Got{k, ""}, fr.caller_rt(k)), {==})))))

def Replace.replace_ffi_verdict(c, d, ic, id, k, f):
  +X = FRp.put_req(FRp.ReqVerdict{c, d, String.eq(ic, id), k}, "")
  Equal.trans(String, FRp.ffi(X), FRp.ffi.of(Wr.Got{FRp.ReqVerdict{c, d, String.eq(ic, id), k}, ""}), FRp.put_verdict(Rp.verdict(Rp.Build.of(c, ic), Rp.Build.of(d, id), k), ""), Equal.cong(Wr.Dec<FRp.Req>, String, FRp.ffi.of, FRp.get_req(X), Wr.Got{FRp.ReqVerdict{c, d, String.eq(ic, id), k}, ""}, fr.rt_verdict(c, d, String.eq(ic, id), k, L.wr_and_l(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), f), L.wr_and_r(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), f))), {==})

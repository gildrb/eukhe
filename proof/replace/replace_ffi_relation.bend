# eukhe: the proof of LAW replace_ffi_relation

import Base
import ../../bend/ffi_replace.bend as FRp
import ../../bend/replace.bend as Rp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/replace.bend as Replace
import ../../laws/wire.bend as Wire
import ../base/bool/and.bend as LBoolAnd
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

# ---- replace: the entry ----

# The proofs of LAWS.bend section `replace: the entry` (the compiled
# core's entry bend/ffi_replace.bend): every request reads back, so the
# entry answers the model's relation and verdict, and the first 65 chars
# of a version decide its rank.

# a Relation request reads back
def fr.rt_rel(+c: String, +d: String, +same: Bool, hc: {LawsBase.wire_fits(String.length(c)) == True{} : Bool}, hd: {LawsBase.wire_fits(String.length(d)) == True{} : Bool}) -> {FRp.get_req(FRp.put_req(FRp.ReqRelation{c, d, same}, "")) == Wr.Got{FRp.ReqRelation{c, d, same}, ""} : Wr.Dec<FRp.Req>}:
  Equal.trans(Wr.Dec<FRp.Req>, FRp.get_req(FRp.put_req(FRp.ReqRelation{c, d, same}, "")), FRp.get_req.of(Wr.Got{0n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, "")))}), Wr.Got{FRp.ReqRelation{c, d, same}, ""}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<FRp.Req>, zq => FRp.get_req.of(zq), Wr.get_nat(Wr.put_nat(0n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, ""))))), Wr.Got{0n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, "")))}, Wire.wire_nat_round_trip(0n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, ""))), {==})), Equal.trans(Wr.Dec<FRp.Req>, FRp.get_req.of(Wr.Got{0n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, "")))}), FRp.get_relation(Wr.Got{c, Wr.put_str(d, Wr.put_bool(same, ""))}), Wr.Got{FRp.ReqRelation{c, d, same}, ""}, Equal.cong(Wr.Dec<String>, Wr.Dec<FRp.Req>, zq => FRp.get_relation(zq), Wr.get_str(Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, "")))), Wr.Got{c, Wr.put_str(d, Wr.put_bool(same, ""))}, Wire.wire_str_round_trip(c, Wr.put_str(d, Wr.put_bool(same, "")), hc)), Equal.trans(Wr.Dec<FRp.Req>, FRp.get_relation(Wr.Got{c, Wr.put_str(d, Wr.put_bool(same, ""))}), FRp.get_relation.d(c, Wr.Got{d, Wr.put_bool(same, "")}), Wr.Got{FRp.ReqRelation{c, d, same}, ""}, Equal.cong(Wr.Dec<String>, Wr.Dec<FRp.Req>, zq => FRp.get_relation.d(c, zq), Wr.get_str(Wr.put_str(d, Wr.put_bool(same, ""))), Wr.Got{d, Wr.put_bool(same, "")}, Wire.wire_str_round_trip(d, Wr.put_bool(same, ""), hd)), Equal.trans(Wr.Dec<FRp.Req>, FRp.get_relation.d(c, Wr.Got{d, Wr.put_bool(same, "")}), FRp.get_relation.same(c, d, Wr.Got{same, ""}), Wr.Got{FRp.ReqRelation{c, d, same}, ""}, Equal.cong(Wr.Dec<Bool>, Wr.Dec<FRp.Req>, zq => FRp.get_relation.same(c, d, zq), Wr.get_bool(Wr.put_bool(same, "")), Wr.Got{same, ""}, Wire.wire_bool_round_trip(same, "")), {==}))))

def Replace.replace_ffi_relation(c, d, ic, id, f):
  +X = FRp.put_req(FRp.ReqRelation{c, d, String.eq(ic, id)}, "")
  Equal.trans(String, FRp.ffi(X), FRp.ffi.of(Wr.Got{FRp.ReqRelation{c, d, String.eq(ic, id)}, ""}), FRp.put_rel(Rp.relation(Rp.Build.of(c, ic), Rp.Build.of(d, id)), ""), Equal.cong(Wr.Dec<FRp.Req>, String, FRp.ffi.of, FRp.get_req(X), Wr.Got{FRp.ReqRelation{c, d, String.eq(ic, id)}, ""}, fr.rt_rel(c, d, String.eq(ic, id), LBoolAnd.wr_and_l(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), f), LBoolAnd.wr_and_r(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), f))), {==})

# eukhe: the proof of LAW semver_ffi_left_over
#
# PROOF of LAW semver_ffi_left_over: a request that fits reads back whole
# before any rest (wire_str_round_trip, and the list loop of
# proof/semver/base.bend: sv_tags_rt); the rest is not empty, so the
# entry answers the left-over error before it looks at the request.

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/semver.bend as Semver
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ./base.bend as LASemver

def slo.release(+c: String, +ts: List<&2, String>, +rest: String, +h: {Semver.release_fits(c, ts) == True{} : Bool}) -> {FSv.get_req(Semver.spell_req_then(FSv.QRelease{c, ts}, rest)) == Wr.Got{FSv.QRelease{c, ts}, rest} : Wr.Dec<FSv.Req>}:
  +hc = LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(c)), Bool.and(LawsBase.wire_fits(List.length(&2, String, ts)), Semver.strs_all(ts)), h)
  +ht = LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(c)), Bool.and(LawsBase.wire_fits(List.length(&2, String, ts)), Semver.strs_all(ts)), h)
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(c, Semver.spell_tags(ts, rest))), Wr.Got{c, Semver.spell_tags(ts, rest)}, Wire.wire_str_round_trip(c, Semver.spell_tags(ts, rest), hc)) : {FSv.get_release(_) == Wr.Got{FSv.QRelease{c, ts}, rest} : Wr.Dec<FSv.Req>}
  %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, Semver.spell_tags(ts, rest)), Wr.Got{ts, rest}, LASemver.sv_tags_rt(ts, rest, ht)) : {FSv.get_release.tags(c, _) == Wr.Got{FSv.QRelease{c, ts}, rest} : Wr.Dec<FSv.Req>}
  {==}

def slo.series(+w: String, +r: String, +rest: String, +h: {Semver.series_fits(w, r) == True{} : Bool}) -> {FSv.get_req(Semver.spell_req_then(FSv.QSeries{w, r}, rest)) == Wr.Got{FSv.QSeries{w, r}, rest} : Wr.Dec<FSv.Req>}:
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(w, Wr.put_str(r, rest))), Wr.Got{w, Wr.put_str(r, rest)}, Wire.wire_str_round_trip(w, Wr.put_str(r, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(w)), LawsBase.wire_fits(String.length(r)), h))) : {FSv.get_series(_) == Wr.Got{FSv.QSeries{w, r}, rest} : Wr.Dec<FSv.Req>}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(r, rest)), Wr.Got{r, rest}, Wire.wire_str_round_trip(r, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(w)), LawsBase.wire_fits(String.length(r)), h))) : {FSv.get_series.release(w, _) == Wr.Got{FSv.QSeries{w, r}, rest} : Wr.Dec<FSv.Req>}
  {==}

# a request that fits reads back whole, the rest after it untouched
def slo.dec(q: FSv.Req, +rest: String, h: {Semver.req_fits(q) == True{} : Bool}) -> {FSv.get_req(Semver.spell_req_then(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FSv.Req>}:
  match q:
    case FSv.QRelease{+c, +ts}:
      slo.release(c, ts, rest, h)
    case FSv.QSeries{+w, +r}:
      slo.series(w, r, rest, h)

def Semver.semver_ffi_left_over(q, rest, fit, more):
  %Equal.sym(Wr.Dec<FSv.Req>, FSv.get_req(Semver.spell_req_then(q, rest)), Wr.Got{q, rest}, slo.dec(q, rest, fit)) : {FSv.ffi.got(_) == Wr.err("semver: input left after the request") : String}
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FSv.ffi.done(q, _) == Wr.err("semver: input left after the request") : String}
  {==}

# eukhe: the proof of LAW semver_ffi_series_long

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/semver.bend as Sv
import ../../bend/wire.bend as Wr
import ../../laws/semver.bend as Semver
import ./base.bend as LASemver

# PROOF of LAW semver_ffi_series_long: the request reads back whole
# (sv_dec_series); a version holds 7 digits in a row, so the guard
# refuses it (sv_req_series).

def Semver.semver_ffi_series_long(w, r, fit, many):
  %Equal.sym(Wr.Dec<FSv.Req>, FSv.get_req(Semver.spell_series(w, r)), Wr.Got{FSv.QSeries{w, r}, ""}, LASemver.sv_dec_series(w, r, fit)) : {FSv.ffi.got(_) == Semver.long_err() : String}
  %Equal.sym(Bool, FSv.short.req(FSv.QSeries{w, r}), False{}, LASemver.sv_not_true(FSv.short.req(FSv.QSeries{w, r}), Bool.or(Semver.seven_spec(w), Semver.seven_spec(r)), LASemver.sv_req_series(w, r), many)) : {FSv.ffi.short(FSv.QSeries{w, r}, _) == Semver.long_err() : String}
  {==}

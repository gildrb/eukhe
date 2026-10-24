# eukhe: the proof of LAW semver_ffi_series

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/semver.bend as Sv
import ../../bend/wire.bend as Wr
import ../../laws/semver.bend as Semver
import ./base.bend as LASemver

# PROOF of LAW semver_ffi_series: the request reads back whole
# (sv_dec_series); the guard passes (sv_req_series); the answer is the
# spec's (sv_series).

def Semver.semver_ffi_series(w, r, fit, few):
  %Equal.sym(Wr.Dec<FSv.Req>, FSv.get_req(Semver.spell_series(w, r)), Wr.Got{FSv.QSeries{w, r}, ""}, LASemver.sv_dec_series(w, r, fit)) : {FSv.ffi.got(_) == Semver.series_spec(w, r) : String}
  %Equal.sym(Bool, FSv.short.req(FSv.QSeries{w, r}), True{}, LASemver.sv_not_false(FSv.short.req(FSv.QSeries{w, r}), Bool.or(Semver.seven_spec(w), Semver.seven_spec(r)), LASemver.sv_req_series(w, r), few)) : {FSv.ffi.short(FSv.QSeries{w, r}, _) == Semver.series_spec(w, r) : String}
  LASemver.sv_series(Sv.Ver.parse(r), Sv.Ver.parse(w))

# eukhe: the proof of LAW semver_ffi_release_long

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/semver.bend as Sv
import ../../bend/wire.bend as Wr
import ../../laws/semver.bend as Semver
import ./base.bend as LASemver

# PROOF of LAW semver_ffi_release_long: the request reads back whole
# (sv_dec_release); a read text holds 7 digits in a row, so the guard
# refuses it (sv_req_release).

def Semver.semver_ffi_release_long(c, ts, fit, many):
  %Equal.sym(Wr.Dec<FSv.Req>, FSv.get_req(Semver.spell_release(c, ts)), Wr.Got{FSv.QRelease{c, ts}, ""}, LASemver.sv_dec_release(c, ts, fit)) : {FSv.ffi.got(_) == Semver.long_err() : String}
  %Equal.sym(Bool, FSv.short.req(FSv.QRelease{c, ts}), False{}, LASemver.sv_not_true(FSv.short.req(FSv.QRelease{c, ts}), Bool.or(Semver.seven_spec(c), Semver.seven_tags(ts)), LASemver.sv_req_release(c, ts), many)) : {FSv.ffi.short(FSv.QRelease{c, ts}, _) == Semver.long_err() : String}
  {==}

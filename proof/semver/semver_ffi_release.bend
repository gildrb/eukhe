# eukhe: the proof of LAW semver_ffi_release

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/semver.bend as Sv
import ../../bend/wire.bend as Wr
import ../../laws/semver.bend as Semver
import ./base.bend as LASemver

# PROOF of LAW semver_ffi_release: the request reads back whole
# (sv_dec_release); no read text holds 7 digits in a row, so the guard
# passes (sv_req_release); the model's release, or why there is none,
# is spelled as the spec spells it (sv_put).

def Semver.semver_ffi_release(c, ts, fit, few):
  %Equal.sym(Wr.Dec<FSv.Req>, FSv.get_req(Semver.spell_release(c, ts)), Wr.Got{FSv.QRelease{c, ts}, ""}, LASemver.sv_dec_release(c, ts, fit)) : {FSv.ffi.got(_) == Semver.release_spec(c, ts) : String}
  %Equal.sym(Bool, FSv.short.req(FSv.QRelease{c, ts}), True{}, LASemver.sv_not_false(FSv.short.req(FSv.QRelease{c, ts}), Bool.or(Semver.seven_spec(c), Semver.seven_tags(ts)), LASemver.sv_req_release(c, ts), few)) : {FSv.ffi.short(FSv.QRelease{c, ts}, _) == Semver.release_spec(c, ts) : String}
  LASemver.sv_put(Sv.Rel.release(c, ts), c, ts)

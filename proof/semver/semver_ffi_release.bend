# eukhe: the proof of LAW semver_ffi_release

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ./base.bend as LASemver

# PROOF of LAW semver_ffi_release: the request reads back whole and passes
# the 7-digit guard (svr.reply); the model's release is r, which the entry
# writes as its version, Tag.of and Rel.title: `eukhe-v` and `Eukhe v`
# before the version written.

def pfr.put(+c: String, +ts: List<&2, String>, +r: Sv.Ver, rel: {Sv.Rel.release(c, ts) == Some{r} : Maybe<&2, Sv.Ver>}) -> {FSv.release.put(Sv.Rel.release(c, ts), c, ts) == Semver.spell_rel(r) : String}:
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Rel.release(c, ts), Some{r}, rel) : {FSv.release.put(_, c, ts) == Semver.spell_rel(r) : String}
  {==}

def Semver.semver_ffi_release(c, ts, fit, few, r, rel):
  LASemver.svr.reply(c, ts, fit, few, Semver.spell_rel(r), pfr.put(c, ts, r, rel))

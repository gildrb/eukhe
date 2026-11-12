# eukhe: the proof of LAW semver_ffi_release_unparsed

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/semver.bend as Sv
import ../../bend/wire.bend as Wr
import ../../laws/semver.bend as Semver
import ./base.bend as LASemver

# PROOF of LAW semver_ffi_release_unparsed: the request reads back whole
# and passes the 7-digit guard (svr.reply); the workspace version reads as
# none, so the model has no release and the entry answers why: reason 0.

def pfu.put(+c: String, +ts: List<&2, String>, +unparsed: {Sv.Ver.parse(c) == None{} : Maybe<&2, Sv.Ver>}) -> {FSv.release.put(Sv.Rel.release(c, ts), c, ts) == Wr.put_nat(0n, "") : String}:
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), None{}, unparsed) : {FSv.release.put(Sv.Rel.release.of(_, ts), c, ts) == Wr.put_nat(0n, "") : String}
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), None{}, unparsed) : {FSv.release.miss(_, ts) == Wr.put_nat(0n, "") : String}
  {==}

def Semver.semver_ffi_release_unparsed(c, ts, fit, few, unparsed):
  LASemver.svr.reply(c, ts, fit, few, Wr.put_nat(0n, ""), pfu.put(c, ts, unparsed))

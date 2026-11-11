# eukhe: the proof of LAW semver_ffi_release_patch

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/semver.bend as Sv
import ../../bend/wire.bend as Wr
import ../../laws/semver.bend as Semver
import ./base.bend as LASemver

# PROOF of LAW semver_ffi_release_patch: the request reads back whole and
# passes the 7-digit guard (svr.reply); the workspace version reads as
# X.Y.(1+z), so the model has no release and the entry answers why:
# reason 1.

def pfp.put(+c: String, +ts: List<&2, String>, +a: Nat, +b: Nat, +z: Nat, +parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 1n+z}} : Maybe<&2, Sv.Ver>}) -> {FSv.release.put(Sv.Rel.release(c, ts), c, ts) == Wr.put_nat(1n, "") : String}:
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), Some{Sv.Ver{a, b, 1n+z}}, parsed) : {FSv.release.put(Sv.Rel.release.of(_, ts), c, ts) == Wr.put_nat(1n, "") : String}
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), Some{Sv.Ver{a, b, 1n+z}}, parsed) : {FSv.release.miss(_, ts) == Wr.put_nat(1n, "") : String}
  {==}

def Semver.semver_ffi_release_patch(c, ts, fit, few, a, b, z, parsed):
  LASemver.svr.reply(c, ts, fit, few, Wr.put_nat(1n, ""), pfp.put(c, ts, a, b, z, parsed))

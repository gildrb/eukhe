# eukhe: the proof of LAW semver_release_refuses_patch_workspace

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver

# a workspace version X.Y.(1+z) releases nothing
def ps.refuse_patch(c: String, +a: Nat, +b: Nat, +z: Nat, +tags: List<&2, String>, parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 1n+z}} : Maybe<&2, Sv.Ver>}) -> {Sv.Rel.release(c, tags) == None{} : Maybe<&2, Sv.Ver>}:
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), Some{Sv.Ver{a, b, 1n+z}}, parsed) : {Sv.Rel.release.of(_, tags) == None{} : Maybe<&2, Sv.Ver>}
  {==}

def Semver.semver_release_refuses_patch_workspace(c, a, b, z, tags, parsed):
  ps.refuse_patch(c, a, b, z, tags, parsed)

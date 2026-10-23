# eukhe: the proof of LAW semver_release_refuses_unparsed_workspace

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver

# a workspace version that is no version releases nothing
def ps.refuse_unparsed(c: String, +tags: List<&2, String>, unparsed: {Sv.Ver.parse(c) == None{} : Maybe<&2, Sv.Ver>}) -> {Sv.Rel.release(c, tags) == None{} : Maybe<&2, Sv.Ver>}:
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), None{}, unparsed) : {Sv.Rel.release.of(_, tags) == None{} : Maybe<&2, Sv.Ver>}
  {==}

def Semver.semver_release_refuses_unparsed_workspace(c, tags, unparsed):
  ps.refuse_unparsed(c, tags, unparsed)

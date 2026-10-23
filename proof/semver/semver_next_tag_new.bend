# eukhe: the proof of LAW semver_next_tag_new

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ./base.bend as LA

def ps.tag_new.go(+s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, e: {Sv.Tag.of(Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))) == t : String}) -> Empty:
  +n = Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))
  +back = Equal.cong(String, Maybe<&2, Sv.Ver>, Sv.Tag.ver, Sv.Tag.of(n), t, e)
  +parsed = Equal.trans(Maybe<&2, Sv.Ver>, Sv.Tag.ver(t), Sv.Tag.ver(Sv.Tag.of(n)), Some{n}, Equal.sym(Maybe<&2, Sv.Ver>, Sv.Tag.ver(Sv.Tag.of(n)), Sv.Tag.ver(t), back), LA.ps.roundtrip(n))
  LA.ps.next_ne(s, xs, t, ys, n, parsed)({==})

# no tag is the tag of the next release
def ps.tag_new(+s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>) -> {Sv.Tag.of(Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))) != t : String}:
  e => ps.tag_new.go(s, xs, t, ys, e)

def Semver.semver_next_tag_new(s, xs, t, ys):
  ps.tag_new(s, xs, t, ys)

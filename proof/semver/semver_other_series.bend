# eukhe: the proof of LAW semver_other_series

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ./base.bend as LA

# a tag of another series changes nothing
def ps.top_skip(+s: Sv.Ver, xs: List<&2, String>, +t: String, +ys: List<&2, String>, h: {Sv.Rel.ofs(s, t) == False{} : Bool}) -> {Sv.Rel.top(s, List.append(&2, String, xs, ys)) == Sv.Rel.top(s, List.append(&2, String, xs, t <> ys)) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      LA.ps.add_skip(s, Sv.Tag.ver(t), Sv.Rel.top(s, ys), h)
    case x <> r:
      %ps.top_skip(s, r, t, ys, h) : {Sv.Rel.add(s, Sv.Tag.ver(x), Sv.Rel.top(s, List.append(&2, String, r, ys))) == Sv.Rel.add(s, Sv.Tag.ver(x), _) : Maybe<&2, Nat>}
      {==}

def ps.other(s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, h: {Sv.Rel.ofs(s, t) == False{} : Bool}) -> {Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) == Sv.Rel.next(s, List.append(&2, String, xs, ys)) : Sv.Ver}:
  match s:
    case Sv.Ver{+a, +b, +c}:
      %ps.top_skip(Sv.Ver{a, b, c}, xs, t, ys, h) : {Sv.Ver{a, b, Sv.Rel.after(_)} == Sv.Ver{a, b, Sv.Rel.after(Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, ys)))} : Sv.Ver}
      {==}

def Semver.semver_other_series(s, xs, t, ys, other):
  ps.other(s, xs, t, ys, other)

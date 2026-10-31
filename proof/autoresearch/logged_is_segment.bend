# eukhe: the proof of LAW logged_is_segment

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../spec/autoresearch/segment.bend as SG
import ../../laws/autoresearch/history.bend as AutoresearchHistory

# one row: the code's count added to the rest is the spec's
def LoggedIsSegment.at(b: Bool, st: Maybe<&2, ArS.Status>, -x: Nat) -> {Nat.add(ArS.one(Bool.and(b, ArS.has(st))), x) == SG.logged_count.at(b, st, x) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case None{}:
          {==}
        case Some{k}:
          {==}

# the code's logged count of a segment is the spec's
def LoggedIsSegment.go(rs: List<&2, ArS.Row>, +seg: Nat) -> {ArS.logged(rs, seg) == SG.logged_count(rs, seg) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case ArS.Row{id, +sg, +st, m, ms, ps, fn, fl, desc} <> t:
      %LoggedIsSegment.go(t, seg) : {Nat.add(ArS.one(Bool.and(Nat.is_eq(sg, seg), ArS.has(st))), ArS.logged(t, seg)) == SG.logged_count.at(Nat.is_eq(sg, seg), st, _) : Nat}
      LoggedIsSegment.at(Nat.is_eq(sg, seg), st, ArS.logged(t, seg))

def AutoresearchHistory.logged_is_segment(s):
  match s:
    case ArS.St{c, +seg, mode, runs, pend}:
      LoggedIsSegment.go(runs, seg)

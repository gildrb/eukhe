# eukhe: the proof of LAW reject_shows_lines

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def pv.cut_eq(b: Bool) -> {Ds.shows.cut(b) == DocSeen.seen.Cut(b) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pv.put_at(+n: Nat, w: Maybe<&2, Nat>, +r: List<&2, Ds.Show>) -> {Ds.shows.put(n, w, r) == DocSeen.seen.Shown.at(n, w, r) : List<&2, Ds.Show>}:
  match w:
    case None{}:
      {==}
    case Some{+x}:
      %pv.cut_eq(Nat.is_le(x, Ds.cols)) : {Ds.Show{n, Ds.shows.cut(Nat.is_le(x, Ds.cols))} <> r == Ds.Show{n, _} <> r : List<&2, Ds.Show>}
      {==}

def pv.shows_eq(us: List<&2, Ds.At>) -> {Ds.shows(us) == DocSeen.seen.Shown(us) : List<&2, Ds.Show>}:
  match us:
    case Nil{}:
      {==}
    case a <> +rest:
      match a:
        case Ds.At{+n, w}:
          %pv.shows_eq(rest) : {Ds.shows.put(n, w, Ds.shows(rest)) == DocSeen.seen.Shown.at(n, w, _) : List<&2, Ds.Show>}
          pv.put_at(n, w, Ds.shows(rest))

def pv.shown_go(+u: List<&2, Ds.At>) -> {Ds.Check.shown(Ds.check.go(u)) == DocSeen.seen.Shown(List.take(&2, Ds.At, u, Ds.cap)) : List<&2, Ds.Show>}:
  pv.shows_eq(List.take(&2, Ds.At, u, Ds.cap))

def DocSeen.reject_shows_lines(seen, ats):
  %LA.pv.unseen_eq(seen, ats) : {Ds.Check.shown(Ds.check(seen, ats)) == DocSeen.seen.Shown(List.take(&2, Ds.At, _, Ds.cap)) : List<&2, Ds.Show>}
  pv.shown_go(Ds.unseen(seen, ats))

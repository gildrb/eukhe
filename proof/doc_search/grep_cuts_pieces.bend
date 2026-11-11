# eukhe: the proof of LAW grep_cuts_pieces
#
# PROOF: by induction on os: an entry's notice (or none) is put before the
# notices of the rest, whatever follows them (cpc.put, per class and cut
# flag). One entry: per class and cut flag, one notice or none.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def cpc.put(i: Nat, c: Sr.Class, b: Bool, -xs: List<&2, Nat>, -ys: List<&2, Nat>) -> {Sr.cut.put(i, c, b, List.append(&2, Nat, xs, ys)) == List.append(&2, Nat, Sr.cut.put(i, c, b, xs), ys) : List<&2, Nat>}:
  match c:
    case Sr.NoMatch{}:
      {==}
    case Sr.Shown{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case Sr.PagedOut{}:
      {==}
    case Sr.Unsearched{}:
      {==}
    case Sr.Skipped{w}:
      {==}

def cpc.app(os: List<&2, Sr.Out>, +qs: List<&2, Sr.Out>) -> {Sr.cuts(List.append(&2, Sr.Out, os, qs)) == List.append(&2, Nat, Sr.cuts(os), Sr.cuts(qs)) : List<&2, Nat>}:
  match os:
    case Nil{}:
      {==}
    case o <> t:
      match o:
        case Sr.Out{+i, +c, +b, pa}:
          Equal.trans(List<&2, Nat>, Sr.cut.put(i, c, b, Sr.cuts(List.append(&2, Sr.Out, t, qs))), Sr.cut.put(i, c, b, List.append(&2, Nat, Sr.cuts(t), Sr.cuts(qs))), List.append(&2, Nat, Sr.cut.put(i, c, b, Sr.cuts(t)), Sr.cuts(qs)), Equal.cong(List<&2, Nat>, List<&2, Nat>, v => Sr.cut.put(i, c, b, v), Sr.cuts(List.append(&2, Sr.Out, t, qs)), List.append(&2, Nat, Sr.cuts(t), Sr.cuts(qs)), cpc.app(t, qs)), cpc.put(i, c, b, Sr.cuts(t), Sr.cuts(qs)))

def cpc.one(o: Sr.Out) -> {(Sr.cuts(Nil{}), Nat.is_le(List.length(&2, Nat, Sr.cuts([o])), 1n)) == (Nil{}, True{}) : List<&2, Nat> & Bool}:
  match o:
    case Sr.Out{i, c, b, pa}:
      match c:
        case Sr.NoMatch{}:
          {==}
        case Sr.Shown{}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}
        case Sr.PagedOut{}:
          {==}
        case Sr.Unsearched{}:
          {==}
        case Sr.Skipped{w}:
          {==}

def DocSearch.grep_cuts_pieces(os, qs, o):
  (cpc.app(os, qs), cpc.one(o))

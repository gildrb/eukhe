# eukhe: the proof of LAW limit_cuts: l < c + s is l < c, or l - c < s; the
# code peels the page's counts off l one file at a time (no sum)

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def lc.lt_add(c: Nat, l: Nat, -s: Nat) -> {Bool.or(Nat.is_lt(l, c), Nat.is_lt(Nat.sub(l, c), s)) == Nat.is_lt(l, Nat.add(c, s)) : Bool}:
  match c l:
    case 0n 0n:
      {==}
    case 0n 1n+m:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+m:
      lc.lt_add(p, m, s)

def lc.over(cs: List<&2, Nat>, +l: Nat) -> {Sr.rr.over(cs, l) == Nat.is_lt(l, DocSearch.ds_sum(cs)) : Bool}:
  match cs:
    case Nil{}:
      match l:
        case 0n:
          {==}
        case 1n+m:
          {==}
    case +c <> t:
      %lc.lt_add(c, l, DocSearch.ds_sum(t)) : {Bool.or(Nat.is_lt(l, c), Sr.rr.over(t, Nat.sub(l, c))) == _ : Bool}
      %lc.over(t, Nat.sub(l, c)) : {Bool.or(Nat.is_lt(l, c), Sr.rr.over(t, Nat.sub(l, c))) == Bool.or(Nat.is_lt(l, c), _) : Bool}
      {==}

def DocSearch.limit_cuts(cs, l):
  lc.over(cs, l)

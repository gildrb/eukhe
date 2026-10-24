# eukhe: the proof of LAW fetch_reaches: the needs of the ranges step alike

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def fetch.need(r: Sr.Range, +base: Nat) -> {Sr.reach(r, base) == DocSearch.ds_need(r, base) : Nat}:
  match r:
    case Sr.Range{a, z}:
      match z:
        case None{}:
          {==}
        case Some{e}:
          {==}

def fetch.needs(rs: List<&2, Sr.Range>, +base: Nat) -> {Sr.reach.top(rs, base) == DocSearch.ds_needs(rs, base) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case +r <> t:
      %fetch.need(r, base) : {Nat.max(Sr.reach(r, base), Sr.reach.top(t, base)) == Nat.max(_, DocSearch.ds_needs(t, base)) : Nat}
      %fetch.needs(t, base) : {Nat.max(Sr.reach(r, base), Sr.reach.top(t, base)) == Nat.max(Sr.reach(r, base), _) : Nat}
      {==}

def DocSearch.fetch_reaches(rs, p, rem, maxb):
  match rs:
    case Nil{}:
      {==}
    case +r <> t:
      %fetch.needs(r <> t, 1n+p) : {Nat.max(1n+p, Nat.min(Sr.reach.top(r <> t, 1n+p), 1n+maxb)) == Nat.max(1n+p, Nat.min(_, 1n+maxb)) : Nat}
      {==}

# eukhe: the proof of LAW grep_seen_counts
#
# PROOF: by cases on the entry and the matches left: a file of matches
# searched is shown or paged out and counts one; every other entry (no
# match, not searched, skipped) counts none.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def sc.page(b: Bool, -n: Nat) -> {1n+n == Nat.add(Nat.add(DocSearch.ds_bit(DocSearch.ds_matching(Sr.page.cls(b))), 0n), n) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sc.skip(rem: Nat, w: Sr.Reason, -n: Nat) -> {n == Nat.add(Nat.add(DocSearch.ds_bit(DocSearch.ds_matching(Sr.skip.cls(w, rem))), 0n), n) : Nat}:
  match rem:
    case 0n:
      match w:
        case Sr.Binary{}:
          {==}
        case Sr.Unreadable{}:
          {==}
        case Sr.Excluded{}:
          {==}
        case Sr.Link{}:
          {==}
        case Sr.Broken{}:
          {==}
    case 1n+r:
      {==}

# an opened file, by the matches left, then the matches it holds
def sc.opened(rem: Nat, h: Nat, i: Nat, big: Bool, +p: Nat, +s: Nat, +k: Nat, +n: Nat) -> {Sr.seen(Sr.Ent{i, Sr.Opened{h, big}}, rem, n) == Nat.add(DocSearch.ds_matched([Sr.out(Sr.Ent{i, Sr.Opened{h, big}}, p, s, k, rem, n)]), n) : Nat}:
  match rem:
    case 0n:
      {==}
    case 1n+r:
      match h:
        case 0n:
          {==}
        case 1n+g:
          sc.page(Sr.onpage(n, s, k), n)

def DocSearch.grep_seen_counts(e, p, s, k, rem, n):
  match e:
    case Sr.Ent{i, f}:
      match f:
        case Sr.Opened{h, big}:
          sc.opened(rem, h, i, big, p, s, k, n)
        case Sr.Skip{w}:
          sc.skip(rem, w, n)

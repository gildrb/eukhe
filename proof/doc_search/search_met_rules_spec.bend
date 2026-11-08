# eukhe: the proof of LAW search_met_rules_spec: by cases on the entry, the matches left
# and the matches of an opened file; a page's class is the spec's pick

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def met.page(b: Bool) -> {DocSearch.ds_cls_if(b, Sr.Shown{}, Sr.PagedOut{}) == Sr.page.cls(b) : Sr.Class}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def DocSearch.search_met_rules_spec(e, p, s, k, rem, n):
  match e:
    case Sr.Ent{i, f}:
      match f:
        case Sr.Opened{h, big}:
          match h rem:
            case 0n 0n:
              {==}
            case 0n 1n+r:
              {==}
            case 1n+g 0n:
              {==}
            case 1n++g 1n++r:
              +b = Bool.and(Nat.is_le(s, n), Nat.is_lt(n, Nat.add(s, k)))
              +ent = {Sr.Ent{i, Sr.Opened{1n+g, big}} : Sr.Ent}
              +kept = Nat.min(1n+g, Nat.min(p, 1n+r))
              -rest = {(kept, (Nat.sub(1n+r, kept), 1n+n)) : Nat & (Nat & Nat)}
              -spec = {(DocSearch.ds_out(ent, p, s, k, 1n+r, n), (DocSearch.ds_kept(ent, p, 1n+r), (Nat.sub(1n+r, DocSearch.ds_kept(ent, p, 1n+r)), DocSearch.ds_seen(ent, 1n+r, n)))) : Sr.Out & (Nat & (Nat & Nat))}
              %met.page(b) : {(Sr.Out{i, _, Nat.is_lt(Nat.min(p, 1n+r), 1n+g), big}, rest) == spec : Sr.Out & (Nat & (Nat & Nat))}
              {==}
        case Sr.Skip{w}:
          match w rem:
            case Sr.Binary{} 0n:
              {==}
            case Sr.Unreadable{} 0n:
              {==}
            case Sr.Excluded{} 0n:
              {==}
            case Sr.Link{} 0n:
              {==}
            case Sr.Broken{} 0n:
              {==}
            case w 1n+r:
              {==}

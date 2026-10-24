# eukhe: the proof of LAW grep_walk_spec: by cases on the entry, the matches left
# and the matches of an opened file; a page's class is the spec's pick

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def walk.page(b: Bool) -> {Sr.page.cls(b) == DocSearch.ds_cls_if(b, Sr.Shown{}, Sr.PagedOut{}) : Sr.Class}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def DocSearch.grep_walk_spec(e, es, p, s, k, rem, n):
  match e:
    case Sr.Ent{i, f}:
      match f:
        case Sr.Opened{h, big}:
          match h:
            case 0n:
              match rem:
                case 0n:
                  {==}
                case 1n+r:
                  {==}
            case 1n+g:
              match rem:
                case 0n:
                  {==}
                case 1n+r:
                  +b = Bool.and(Nat.is_le(s, n), Nat.is_lt(n, Nat.add(s, k)))
                  %walk.page(b) : {(Nil{}, Sr.Out{i, Sr.page.cls(b), Nat.is_lt(Nat.min(p, 1n+r), 1n+g), big} <> Sr.run(es, p, s, k, Nat.sub(1n+r, Nat.min(1n+g, Nat.min(p, 1n+r))), 1n+n)) == (Nil{}, Sr.Out{i, _, Nat.is_lt(Nat.min(p, 1n+r), 1n+g), big} <> Sr.run(es, p, s, k, Nat.sub(1n+r, Nat.min(1n+g, Nat.min(p, 1n+r))), 1n+n)) : List<&2, Sr.Out> & List<&2, Sr.Out>}
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

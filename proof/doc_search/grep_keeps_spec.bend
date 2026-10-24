# eukhe: the proof of LAW grep_keeps_spec: entry by entry; a skipped entry keeps
# none, so rem - 0 is rem

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def keeps.sub0(c: Nat) -> {c == Nat.sub(c, 0n) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+q:
      {==}

def keeps.go(es: List<&2, Sr.Ent>, +p: Nat, +rem: Nat) -> {Sr.keeps(es, p, rem) == DocSearch.ds_keeps(es, p, rem) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Sr.Ent{i, f}:
          match f:
            case Sr.Opened{+h, big}:
              +r2 = Nat.sub(rem, Nat.min(h, Nat.min(p, rem)))
              %keeps.go(rest, p, r2) : {Nat.min(h, Nat.min(p, rem)) <> Sr.keeps(rest, p, r2) == Nat.min(h, Nat.min(p, rem)) <> _ : List<&2, Nat>}
              {==}
            case Sr.Skip{w}:
              %keeps.sub0(rem) : {0n <> Sr.keeps(rest, p, rem) == 0n <> DocSearch.ds_keeps(rest, p, _) : List<&2, Nat>}
              %keeps.go(rest, p, rem) : {0n <> Sr.keeps(rest, p, rem) == 0n <> _ : List<&2, Nat>}
              {==}

def DocSearch.grep_keeps_spec(es, p, rem):
  keeps.go(es, p, rem)

# eukhe: the proof of LAW edit_count_is_newlines
#
# PROOF: the count of a body put before another steps byte by byte with
# the first body (a `\n` adds 1, any other byte nothing); the single bytes
# compute.

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines

def ecn.app(a: List<&2, Dl.B>, +b: List<&2, Dl.B>) -> {Dl.lfs(List.append(&2, Dl.B, a, b)) == Nat.add(Dl.lfs(a), Dl.lfs(b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case Dl.A{}:
          ecn.app(t, b)
        case Dl.R{}:
          ecn.app(t, b)
        case Dl.N{}:
          %ecn.app(t, b) : {1n+Dl.lfs(List.append(&2, Dl.B, t, b)) == 1n+_ : Nat}
          {==}

def DocLines.edit_count_is_newlines(a, b):
  (ecn.app(a, b), {==})

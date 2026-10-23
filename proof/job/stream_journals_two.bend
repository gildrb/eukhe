# eukhe: the proof of LAW stream_journals_two

import Base
import ../../bend/job.bend as Jb
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pj.two(es: List<&2, Jb.CEv>, +b: Nat, +w: Nat, +u: Nat) -> {Nat.is_le(List.length(&2, Jb.CRec, Jb.c.go(es, Jb.Open{b, w, u})), 1n) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Jb.Delta{n}:
          pj.two(rest, Nat.add(b, n), w, u)
        case Jb.Warn{}:
          pj.two(rest, b, 1n+w, u)
        case Jb.Use{n}:
          pj.two(rest, b, w, Nat.add(u, n))
        case Jb.Final{}:
          %LA.pj.cshut(rest) : {Nat.is_le(1n+List.length(&2, Jb.CRec, _), 1n) == True{} : Bool}
          {==}
        case Jb.Cancel{}:
          %LA.pj.cshut(rest) : {Nat.is_le(1n+List.length(&2, Jb.CRec, _), 1n) == True{} : Bool}
          {==}

def pj.stream_journals_two(es: List<&2, Jb.CEv>) -> {Nat.is_le(List.length(&2, Jb.CRec, Jb.journal(es)), 2n) == True{} : Bool}:
  pj.two(es, 0n, 0n, 0n)

def Laws.stream_journals_two(es):
  pj.stream_journals_two(es)

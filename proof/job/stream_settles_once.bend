# eukhe: the proof of LAW stream_settles_once

import Base
import ../../bend/job.bend as Jb
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pj.sett(es: List<&2, Jb.CEv>, +b: Nat, +w: Nat, +u: Nat) -> {Jb.settles(Jb.c.go(es, Jb.Open{b, w, u})) == Jb.once(Jb.c.ends(es)) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Jb.Delta{n}:
          pj.sett(rest, Nat.add(b, n), w, u)
        case Jb.Warn{}:
          pj.sett(rest, b, 1n+w, u)
        case Jb.Use{n}:
          pj.sett(rest, b, w, Nat.add(u, n))
        case Jb.Final{}:
          %LA.pj.cshut(rest) : {1n+Jb.settles(_) == 1n : Nat}
          {==}
        case Jb.Cancel{}:
          %LA.pj.cshut(rest) : {1n+Jb.settles(_) == 1n : Nat}
          {==}

def pj.stream_settles_once(+es: List<&2, Jb.CEv>) -> {Jb.settles(Jb.journal(es)) == Jb.once(Jb.c.ends(es)) : Nat}:
  pj.sett(es, 0n, 0n, 0n)

def Laws.stream_settles_once(es):
  pj.stream_settles_once(es)

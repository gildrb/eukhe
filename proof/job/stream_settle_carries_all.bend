# eukhe: the proof of LAW stream_settle_carries_all

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def pj.carry(es: List<&2, Jb.CEv>, +b: Nat, +w: Nat, +u: Nat, h: {Jb.c.ends(es) == True{} : Bool}) -> {Jb.carried(Jb.c.go(es, Jb.Open{b, w, u})) == Some{Jb.Tally{Nat.add(b, Jb.c.bytes(es)), Nat.add(w, Jb.c.warns(es)), Nat.add(u, Jb.c.usage(es))}} : Maybe<&2, Jb.Tally>}:
  match es:
    case Nil{}:
      LLogicLogic.pj.absurdF({Jb.carried(Nil{}) == Some{Jb.Tally{Nat.add(b, 0n), Nat.add(w, 0n), Nat.add(u, 0n)}} : Maybe<&2, Jb.Tally>}, h)
    case e <> +rest:
      match e:
        case Jb.Delta{+n}:
          %LA.pj.add_assoc(b, n, Jb.c.bytes(rest)) : {Jb.carried(Jb.c.go(rest, Jb.Open{Nat.add(b, n), w, u})) == Some{Jb.Tally{_, Nat.add(w, Jb.c.warns(rest)), Nat.add(u, Jb.c.usage(rest))}} : Maybe<&2, Jb.Tally>}
          pj.carry(rest, Nat.add(b, n), w, u, h)
        case Jb.Warn{}:
          %LA.pj.add_succ(w, Jb.c.warns(rest)) : {Jb.carried(Jb.c.go(rest, Jb.Open{b, 1n+w, u})) == Some{Jb.Tally{Nat.add(b, Jb.c.bytes(rest)), _, Nat.add(u, Jb.c.usage(rest))}} : Maybe<&2, Jb.Tally>}
          pj.carry(rest, b, 1n+w, u, h)
        case Jb.Use{+n}:
          %LA.pj.add_assoc(u, n, Jb.c.usage(rest)) : {Jb.carried(Jb.c.go(rest, Jb.Open{b, w, Nat.add(u, n)})) == Some{Jb.Tally{Nat.add(b, Jb.c.bytes(rest)), Nat.add(w, Jb.c.warns(rest)), _}} : Maybe<&2, Jb.Tally>}
          pj.carry(rest, b, w, Nat.add(u, n), h)
        case Jb.Final{}:
          %LA.pj.add_zero(b) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{_, Nat.add(w, 0n), Nat.add(u, 0n)}} : Maybe<&2, Jb.Tally>}
          %LA.pj.add_zero(w) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{b, _, Nat.add(u, 0n)}} : Maybe<&2, Jb.Tally>}
          %LA.pj.add_zero(u) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{b, w, _}} : Maybe<&2, Jb.Tally>}
          {==}
        case Jb.Cancel{}:
          %LA.pj.add_zero(b) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{_, Nat.add(w, 0n), Nat.add(u, 0n)}} : Maybe<&2, Jb.Tally>}
          %LA.pj.add_zero(w) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{b, _, Nat.add(u, 0n)}} : Maybe<&2, Jb.Tally>}
          %LA.pj.add_zero(u) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{b, w, _}} : Maybe<&2, Jb.Tally>}
          {==}

def pj.stream_settle_carries_all(+es: List<&2, Jb.CEv>, ended: {Jb.c.ends(es) == True{} : Bool}) -> {Jb.carried(Jb.journal(es)) == Some{Jb.Tally{Jb.c.bytes(es), Jb.c.warns(es), Jb.c.usage(es)}} : Maybe<&2, Jb.Tally>}:
  pj.carry(es, 0n, 0n, 0n, ended)

def Job.stream_settle_carries_all(es, ended):
  pj.stream_settle_carries_all(es, ended)

# eukhe: the proof of LAW job_cap_drops_only_excess

import Base
import ../../bend/job.bend as Jb
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def pj.le_addl(n: Nat, +p: Nat, m: Nat, h: {Nat.is_le(Nat.add(n, p), m) == True{} : Bool}) -> {Nat.is_le(n, m) == True{} : Bool}:
  match n m:
    case 0n _:
      L.pj.le0(m)
    case 1n+np 0n:
      L.pj.absurdF({Nat.is_le(1n+np, 0n) == True{} : Bool}, h)
    case 1n+np 1n+mp:
      pj.le_addl(np, p, mp, h)

# the room left under the cap shrinks by the output that fits
def pj.fit_room(+c: Nat, +k: Nat, +n: Nat, +p: Nat, h: {Nat.is_le(Nat.add(n, p), Nat.sub(c, k)) == True{} : Bool}) -> {Nat.is_le(p, Nat.sub(c, Nat.add(k, n))) == True{} : Bool}:
  %LA.pj.sub_sub(c, k, n) : {Nat.is_le(p, _) == True{} : Bool}
  LA.pj.le_sub(n, p, Nat.sub(c, k), h)

def pj.room0(+c: Nat, -es: List<&2, Jb.JEv>, fits: {Nat.is_le(Jb.produced(es), c) == True{} : Bool}) -> {Nat.is_le(Jb.produced(es), Nat.sub(c, 0n)) == True{} : Bool}:
  %L.pj.sub_zero(c) : {Nat.is_le(Jb.produced(es), _) == True{} : Bool}
  fits

# output that fits the room left under the cap drops nothing
def pj.fit(es: List<&2, Jb.JEv>, +c: Nat, +k: Nat, +h: {Nat.is_le(Jb.produced(es), Nat.sub(c, k)) == True{} : Bool}) -> {Jb.J.dropped(Jb.go(es, Some{c}, Jb.Live{k, 0n})) == 0n : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Jb.Out{+n}:
          %L.pj.min_of_le(n, Nat.sub(c, k), pj.le_addl(n, Jb.produced(rest), Nat.sub(c, k), h)) : {Jb.J.dropped(Jb.go(rest, Some{c}, Jb.Live{Nat.add(k, _), Nat.sub(n, _)})) == 0n : Nat}
          %LA.pj.sub_self(n) : {Jb.J.dropped(Jb.go(rest, Some{c}, Jb.Live{Nat.add(k, n), _})) == 0n : Nat}
          pj.fit(rest, c, Nat.add(k, n), pj.fit_room(c, k, n, Jb.produced(rest), h))
        case Jb.Quit{q}:
          %LA.pj.ended(rest, Some{c}, k, 0n, Jb.Exited{q}) : {Jb.J.dropped(_) == 0n : Nat}
          {==}
        case Jb.Kill{}:
          %LA.pj.ended(rest, Some{c}, k, 0n, Jb.Killed{}) : {Jb.J.dropped(_) == 0n : Nat}
          {==}
        case Jb.Tick{}:
          pj.fit(rest, c, k, h)

def pj.job_cap_drops_only_excess(+c: Nat, +es: List<&2, Jb.JEv>, fits: {Nat.is_le(Jb.produced(es), c) == True{} : Bool}) -> {Jb.J.dropped(Jb.run(Some{c}, es)) == 0n : Nat}:
  pj.fit(es, c, 0n, pj.room0(c, es, fits))

def Laws.job_cap_drops_only_excess(c, es, fits):
  pj.job_cap_drops_only_excess(c, es, fits)

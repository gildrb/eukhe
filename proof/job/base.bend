# eukhe: lemmas the proofs of area job share

import Base
import ../../bend/job.bend as Jb
import ../base.bend as L

def pj.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pj.le_refl(p)

def pj.add_zero(x: Nat) -> {x == Nat.add(x, 0n) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %pj.add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def pj.add_succ(a: Nat, +b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pj.add_succ(p, b) : {1n+1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def pj.add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pj.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def pj.swap(+x: Nat, +y: Nat, +s: Nat) -> {Nat.add(x, Nat.add(y, s)) == Nat.add(y, Nat.add(x, s)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %pj.add_succ(y, Nat.add(p, s)) : {1n+Nat.add(p, Nat.add(y, s)) == _ : Nat}
      %pj.swap(p, y, s) : {1n+Nat.add(p, Nat.add(y, s)) == 1n+_ : Nat}
      {==}

def pj.swap4(k: Nat, +t: Nat, +d: Nat, +s: Nat) -> {Nat.add(Nat.add(k, d), Nat.add(t, s)) == Nat.add(Nat.add(k, t), Nat.add(d, s)) : Nat}:
  match k:
    case 0n:
      pj.swap(d, t, s)
    case 1n+p:
      %pj.swap4(p, t, d, s) : {1n+Nat.add(Nat.add(p, d), Nat.add(t, s)) == 1n+_ : Nat}
      {==}

def pj.sub_self(n: Nat) -> {0n == Nat.sub(n, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pj.sub_self(p)

def pj.sub_sub(c: Nat, k: Nat, +n: Nat) -> {Nat.sub(Nat.sub(c, k), n) == Nat.sub(c, Nat.add(k, n)) : Nat}:
  match c k:
    case 0n _:
      {==}
    case 1n+cp 0n:
      {==}
    case 1n+cp 1n+kp:
      pj.sub_sub(cp, kp, n)

def pj.add_sub(t: Nat, n: Nat, le: {Nat.is_le(t, n) == True{} : Bool}) -> {n == Nat.add(t, Nat.sub(n, t)) : Nat}:
  match t n:
    case 0n _:
      L.pj.sub_zero(n)
    case 1n+tp 0n:
      L.pj.absurdF({0n == Nat.add(1n+tp, Nat.sub(0n, 1n+tp)) : Nat}, le)
    case 1n+tp 1n+np:
      %pj.add_sub(tp, np, le) : {1n+np == 1n+_ : Nat}
      {==}

def pj.min_le_l(n: Nat, m: Nat) -> {Nat.is_le(Nat.min(n, m), n) == True{} : Bool}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      {==}
    case 1n+np 1n+mp:
      pj.min_le_l(np, mp)

def pj.le_sub(n: Nat, +p: Nat, m: Nat, h: {Nat.is_le(Nat.add(n, p), m) == True{} : Bool}) -> {Nat.is_le(p, Nat.sub(m, n)) == True{} : Bool}:
  match n m:
    case 0n 0n:
      h
    case 0n 1n+mp:
      h
    case 1n+np 0n:
      L.pj.absurdF({Nat.is_le(p, 0n) == True{} : Bool}, h)
    case 1n+np 1n+mp:
      pj.le_sub(np, p, mp, h)

def pj.take_le(cap: Maybe<&2, Nat>, +k: Nat, +n: Nat) -> {Nat.is_le(Jb.take(cap, k, n), n) == True{} : Bool}:
  match cap:
    case None{}:
      pj.le_refl(n)
    case Some{c}:
      pj.min_le_l(n, Nat.sub(c, k))

# an output of n bytes adds n to the bytes kept plus dropped
def pj.split(+k: Nat, +d: Nat, +t: Nat, +n: Nat, le: {Nat.is_le(t, n) == True{} : Bool}) -> {Nat.add(Nat.add(k, d), n) == Nat.add(Nat.add(k, t), Nat.add(d, Nat.sub(n, t))) : Nat}:
  %pj.swap4(k, t, d, Nat.sub(n, t)) : {Nat.add(Nat.add(k, d), n) == _ : Nat}
  %pj.add_sub(t, n, le) : {Nat.add(Nat.add(k, d), n) == Nat.add(Nat.add(k, d), _) : Nat}
  {==}

# Jobs
# ----

# an ended job stays as it ended
def pj.ended(es: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +x: Jb.End) -> {Jb.Ended{k, d, x} == Jb.go(es, cap, Jb.Ended{k, d, x}) : Jb.J}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      pj.ended(rest, cap, k, d, x)

# an ended job reports no more ends
def pj.ends_ended(es: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +x: Jb.End) -> {Nil{} == Jb.ends.go(es, cap, Jb.Ended{k, d, x}) : List<&2, Jb.End>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      pj.ends_ended(rest, cap, k, d, x)

# Streams
# -------

# a settled call journals nothing more
def pj.cshut(es: List<&2, Jb.CEv>) -> {Nil{} == Jb.c.go(es, Jb.Shut{}) : List<&2, Jb.CRec>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      pj.cshut(rest)

# Rewinds
# -------

def pj.id_stop(h: Bool, +i: Nat, +r: Bool) -> {i == Jb.Slot.id(Jb.stop.at(h, Jb.Slot{i, r})) : Nat}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def pj.sub_sub_r(+t: Nat, +k: Nat, +d: Nat) -> {Nat.sub(t, Nat.add(k, d)) == Nat.sub(Nat.sub(t, k), d) : Nat}:
  Equal.sym(Nat, Nat.sub(Nat.sub(t, k), d), Nat.sub(t, Nat.add(k, d)), pj.sub_sub(t, k, d))

# the total of an output step: the old total plus the output
def pj.out_total(+cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +m: Nat) -> {Nat.add(Nat.add(k, d), m) == Jb.J.total(Jb.step(cap, Jb.Live{k, d}, Jb.Out{m})) : Nat}:
  pj.split(k, d, Jb.take(cap, k, m), m, pj.take_le(cap, k, m))

# eukhe: the proof of LAW layout_whole_when_room

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen
import ../base.bend as L

def ps.le_assoc(y: Nat, +h: Nat, +s: Nat, rows: Nat, f: {Nat.is_le(Nat.add(y, Nat.add(h, s)), rows) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(y, h), s), rows) == True{} : Bool}:
  match y rows:
    case 0n _:
      f
    case 1n+p 0n:
      L.screen.ps.absurdF({Nat.is_le(Nat.add(Nat.add(1n+p, h), s), 0n) == True{} : Bool}, f)
    case 1n+p 1n+rp:
      ps.le_assoc(p, h, s, rp, f)

def ps.le_addl(n: Nat, +p: Nat, m: Nat, h: {Nat.is_le(Nat.add(n, p), m) == True{} : Bool}) -> {Nat.is_le(n, m) == True{} : Bool}:
  match n m:
    case 0n _:
      L.ps.le0(m)
    case 1n+np 0n:
      L.screen.ps.absurdF({Nat.is_le(1n+np, 0n) == True{} : Bool}, h)
    case 1n+np 1n+mp:
      ps.le_addl(np, p, mp, h)

def ps.le_sub(n: Nat, +p: Nat, m: Nat, h: {Nat.is_le(Nat.add(n, p), m) == True{} : Bool}) -> {Nat.is_le(p, Nat.sub(m, n)) == True{} : Bool}:
  match n m:
    case 0n 0n:
      h
    case 0n 1n+mp:
      h
    case 1n+np 0n:
      L.screen.ps.absurdF({Nat.is_le(p, 0n) == True{} : Bool}, h)
    case 1n+np 1n+mp:
      ps.le_sub(np, p, mp, h)

def ps.min_of_le(n: Nat, m: Nat, h: {Nat.is_le(n, m) == True{} : Bool}) -> {Nat.min(n, m) == n : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      L.screen.ps.absurdF({Nat.min(1n+np, 0n) == 1n+np : Nat}, h)
    case 1n+np 1n+mp:
      %ps.min_of_le(np, mp, h) : {1n+Nat.min(np, mp) == 1n+_ : Nat}
      {==}

def ps.ncons(-a: Nat, -b: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>, e1: {a == b : Nat}, e2: {xs == ys : List<&2, Nat>}) -> {a <> xs == b <> ys : List<&2, Nat>}:
  %e1 : {a <> xs == _ <> ys : List<&2, Nat>}
  %e2 : {a <> xs == a <> _ : List<&2, Nat>}
  {==}

def ps.layout_whole_when_room(+hs: List<&2, Nat>, +y: Nat, +rows: Nat, fits: {Nat.is_le(Nat.add(y, Sc.sum(hs)), rows) == True{} : Bool}) -> {Sc.heights(Sc.vstack(hs, y, rows)) == hs : List<&2, Nat>}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      +f2 = ps.le_assoc(y, h, Sc.sum(rest), rows, fits)
      +hl = ps.le_sub(y, h, rows, ps.le_addl(Nat.add(y, h), Sc.sum(rest), rows, f2))
      ps.ncons(Nat.min(h, Nat.sub(rows, y)), h, Sc.heights(Sc.vstack(rest, Nat.add(y, h), rows)), rest, ps.min_of_le(h, Nat.sub(rows, y), hl), ps.layout_whole_when_room(rest, Nat.add(y, h), rows, f2))

def Screen.layout_whole_when_room(hs, y, rows, fits):
  ps.layout_whole_when_room(hs, y, rows, fits)

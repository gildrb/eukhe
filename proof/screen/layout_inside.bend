# eukhe: the proof of LAW layout_inside

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen
import ../base.bend as L
import ./base.bend as LA

def screen.ps.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def ps.min_le_r(n: Nat, m: Nat) -> {Nat.is_le(Nat.min(n, m), m) == True{} : Bool}:
  match n m:
    case 0n _:
      L.ps.le0(m)
    case 1n+np 0n:
      {==}
    case 1n+np 1n+mp:
      ps.min_le_r(np, mp)

# 4. Layout
# ---------

# one child placed at row y ends inside the viewport, or is not shown
def ps.inside_one(+y: Nat, +rows: Nat, +h: Nat) -> {Bool.or(Nat.is_eq(Nat.min(h, Nat.sub(rows, y)), 0n), Nat.is_le(Nat.add(y, Nat.min(h, Nat.sub(rows, y))), rows)) == True{} : Bool}:
  match y rows:
    case 0n 0n:
      match h:
        case 0n:
          {==}
        case 1n+hp:
          {==}
    case 0n 1n+rp:
      screen.ps.or_tr(Nat.is_eq(Nat.min(h, 1n+rp), 0n), Nat.is_le(Nat.min(h, 1n+rp), 1n+rp), ps.min_le_r(h, 1n+rp))
    case 1n+yp 0n:
      match h:
        case 0n:
          {==}
        case 1n+hp:
          {==}
    case 1n+yp 1n+rp:
      ps.inside_one(yp, rp, h)

def ps.layout_inside(hs: List<&2, Nat>, +y: Nat, +rows: Nat) -> {Sc.inside(Sc.vstack(hs, y, rows), rows) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      +m = Nat.min(h, Nat.sub(rows, y))
      LA.screen.ps.and_t(Bool.or(Nat.is_eq(m, 0n), Nat.is_le(Nat.add(y, m), rows)), Sc.inside(Sc.vstack(rest, Nat.add(y, h), rows), rows), ps.inside_one(y, rows, h), ps.layout_inside(rest, Nat.add(y, h), rows))

def Screen.layout_inside(hs, y, rows):
  ps.layout_inside(hs, y, rows)

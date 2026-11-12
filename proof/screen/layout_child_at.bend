# eukhe: the proof of LAW layout_child_at
#
# PROOF: induction on the heights and the index: child 0 is placed at the
# start row; child 1 + j of h <> rest is child j of rest stacked from
# y + h, and (above + (y + h)) = ((h + above) + y) by commutativity and
# associativity (layout.shift).

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen/interface.bend as Screen

def layout.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %layout.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def layout.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %layout.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def layout.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, layout.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), layout.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %layout.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def layout.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %layout.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def layout.shift(+a: Nat, +y: Nat, +h: Nat) -> {Nat.add(a, Nat.add(y, h)) == Nat.add(Nat.add(h, a), y) : Nat}:
  %layout.add_comm(a, h) : {Nat.add(a, Nat.add(y, h)) == Nat.add(_, y) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, h), y), Nat.add(a, Nat.add(h, y)), layout.add_assoc(a, h, y)) : {Nat.add(a, Nat.add(y, h)) == _ : Nat}
  %layout.add_comm(y, h) : {Nat.add(a, Nat.add(y, h)) == Nat.add(a, _) : Nat}
  {==}

def layout.at(hs: List<&2, Nat>, +y: Nat, +rows: Nat, i: Nat) -> {Screen.layout_rect_at(Sc.vstack(hs, y, rows), i) == Screen.layout_place(Screen.layout_height_at(hs, i), Nat.add(Screen.layout_above(hs, i), y), rows) : Maybe<&2, Sc.Rect>}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      match i:
        case 0n:
          {==}
        case 1n++j:
          %layout.shift(Screen.layout_above(rest, j), y, h) : {Screen.layout_rect_at(Sc.vstack(rest, Nat.add(y, h), rows), j) == Screen.layout_place(Screen.layout_height_at(rest, j), _, rows) : Maybe<&2, Sc.Rect>}
          layout.at(rest, Nat.add(y, h), rows, j)

def Screen.layout_child_at(hs, y, rows, i):
  layout.at(hs, y, rows, i)

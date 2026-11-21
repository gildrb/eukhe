# eukhe.com's Neovim: the proof of LAW yank_either_way
# ====================================================
#
# Vis.lo and Vis.hi pick the same end whichever way round they get the
# two: line by line, then column by column (Pos.sym, Col.sym), the positions equal
# when neither comes first.

import Base
import ../../../vim/types.bend as T
import ../../../vim/visual.bend as Vi
import ../../../laws/vim/visual.bend as VisualLaws

# the earlier and the later of two columns on one line, either way round
def Col.sym(c1: Nat, c2: Nat, -P: Nat -> T.Pos) -> {(Bool.pick(T.Pos, Nat.is_le(c1, c2), P(c1), P(c2)), Bool.pick(T.Pos, Nat.is_le(c1, c2), P(c2), P(c1))) == (Bool.pick(T.Pos, Nat.is_le(c2, c1), P(c2), P(c1)), Bool.pick(T.Pos, Nat.is_le(c2, c1), P(c1), P(c2))) : (T.Pos & T.Pos)}:
  match c1 c2:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Col.sym(p, q, x => P(1n+x))

# the same for positions: the line first, then the column
def Pos.sym(l1: Nat, l2: Nat, +c1: Nat, +c2: Nat, -P: Nat -> Nat -> T.Pos)
  -> {(Bool.pick(T.Pos, Bool.or(Nat.is_lt(l1, l2), Bool.and(Nat.is_eq(l1, l2), Nat.is_le(c1, c2))), P(l1, c1), P(l2, c2)), Bool.pick(T.Pos, Bool.or(Nat.is_lt(l1, l2), Bool.and(Nat.is_eq(l1, l2), Nat.is_le(c1, c2))), P(l2, c2), P(l1, c1)))
      == (Bool.pick(T.Pos, Bool.or(Nat.is_lt(l2, l1), Bool.and(Nat.is_eq(l2, l1), Nat.is_le(c2, c1))), P(l2, c2), P(l1, c1)), Bool.pick(T.Pos, Bool.or(Nat.is_lt(l2, l1), Bool.and(Nat.is_eq(l2, l1), Nat.is_le(c2, c1))), P(l1, c1), P(l2, c2))) : (T.Pos & T.Pos)}:
  match l1 l2:
    case 0n 0n:
      Col.sym(c1, c2, x => P(0n, x))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Pos.sym(p, q, c1, c2, x => y => P(1n+x, y))

def Ends.sym(a: T.Pos, b: T.Pos) -> {(Vi.Vis.lo(a, b), Vi.Vis.hi(a, b)) == (Vi.Vis.lo(b, a), Vi.Vis.hi(b, a)) : (T.Pos & T.Pos)}:
  match a b:
    case T.Pos{l1, +c1} T.Pos{l2, +c2}:
      Pos.sym(l1, l2, c1, c2, x => y => T.Pos{x, y})

def Text.of(+k: T.Vis, +ls: List<&2, String>, e: (T.Pos & T.Pos)) -> String:
  match e:
    case (p, q):
      Vi.Vis.cut(Vi.Vis.join(ls), Vi.Vis.ends(k, ls, p, q))

def Text.sym(+k: T.Vis, +ls: List<&2, String>, +a: T.Pos, +b: T.Pos) -> {Vi.Vis.text(k, ls, a, b) == Vi.Vis.text(k, ls, b, a) : String}:
  Equal.cong((T.Pos & T.Pos), String, e => Text.of(k, ls, e), (Vi.Vis.lo(a, b), Vi.Vis.hi(a, b)), (Vi.Vis.lo(b, a), Vi.Vis.hi(b, a)), Ends.sym(a, b))

def VisualLaws.yank_either_way(k, ls, a, b):
  Text.sym(k, ls, a, b)

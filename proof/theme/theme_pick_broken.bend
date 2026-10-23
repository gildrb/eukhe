# eukhe: the proof of LAW theme_pick_broken

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pt.keepn(c: Bool, at: Nat, -r: List<&2, Nat>, -s: List<&2, Nat>, e: {r == s : List<&2, Nat>}) -> {T.broken.keep(c, at, r) == List.append(&2, Nat, Laws.th.keepn(c, at), s) : List<&2, Nat>}:
  match c:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, xs => at <> xs, r, s, e)
    case False{}:
      e

def pt.broken_of(l: T.Ld, +skip: Maybe<&2, Nat>, +at: Nat, -r: List<&2, Nat>, -s: List<&2, Nat>, e: {r == s : List<&2, Nat>})
  -> {T.broken.of(l, skip, at, r) == List.append(&2, Nat, Laws.th.keepn(Bool.and(Laws.th.broke(l), Bool.not(Laws.th.is.at(skip, at))), at), s) : List<&2, Nat>}:
  match l:
    case T.Fine{nm, c}:
      e
    case T.Broke{nm, st}:
      match skip:
        case None{}:
          pt.keepn(True{}, at, r, s, e)
        case Some{x}:
          pt.keepn(Bool.not(Nat.is_eq(x, at)), at, r, s, e)

def pt.broken(ls: List<&2, T.Ld>, +skip: Maybe<&2, Nat>, +at: Nat) -> {T.broken(ls, skip, at) == Laws.th.broken(ls, skip, at) : List<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      pt.broken_of(l, skip, at, T.broken(rest, skip, 1n+at), Laws.th.broken(rest, skip, 1n+at), pt.broken(rest, skip, 1n+at))

def pt.broken_w(w: Bool, +id: U32, +ls: List<&2, T.Ld>, +n: String) -> {Laws.th.broken.of(T.pick.warn(w, id, ls, n)) == Laws.th.broken(ls, Laws.th.skip(w, Laws.th.blame(ls, n, 0n)), 0n) : List<&2, Nat>}:
  match w:
    case True{}:
      %Equal.sym(Maybe<&2, Nat>, T.cause.go(ls, n, 0n), Laws.th.blame(ls, n, 0n), LA.pt.cause_go(ls, n, 0n)) : {T.broken(ls, _, 0n) == Laws.th.broken(ls, Laws.th.blame(ls, n, 0n), 0n) : List<&2, Nat>}
      pt.broken(ls, Laws.th.blame(ls, n, 0n), 0n)
    case False{}:
      pt.broken(ls, None{}, 0n)

def Laws.theme_pick_broken(ls, n, id, w, r):
  %Equal.sym(T.Pick, T.pick(ls, n), T.pick.warn(w, id, ls, n), LA.pt.pick_w(ls, n, id, w, r)) : {Laws.th.broken.of(_) == Laws.th.broken(ls, Laws.th.skip(w, Laws.th.blame(ls, n, 0n)), 0n) : List<&2, Nat>}
  pt.broken_w(w, id, ls, n)

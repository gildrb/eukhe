# eukhe: the proof of LAW theme_pick_broken

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pt.keepn(c: Bool, at: Nat, -r: List<&2, Nat>, -s: List<&2, Nat>, e: {r == s : List<&2, Nat>}) -> {TChoice.broken.keep(c, at, r) == List.append(&2, Nat, Theme.th.keepn(c, at), s) : List<&2, Nat>}:
  match c:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, xs => at <> xs, r, s, e)
    case False{}:
      e

def pt.broken_of(l: TChoice.Ld, +skip: Maybe<&2, Nat>, +at: Nat, -r: List<&2, Nat>, -s: List<&2, Nat>, e: {r == s : List<&2, Nat>})
  -> {TChoice.broken.of(l, skip, at, r) == List.append(&2, Nat, Theme.th.keepn(Bool.and(Theme.th.broke(l), Bool.not(Theme.th.is.at(skip, at))), at), s) : List<&2, Nat>}:
  match l:
    case TChoice.Fine{nm, c}:
      e
    case TChoice.Broke{nm, st}:
      match skip:
        case None{}:
          pt.keepn(True{}, at, r, s, e)
        case Some{x}:
          pt.keepn(Bool.not(Nat.is_eq(x, at)), at, r, s, e)

def pt.broken(ls: List<&2, TChoice.Ld>, +skip: Maybe<&2, Nat>, +at: Nat) -> {TChoice.broken(ls, skip, at) == Theme.th.broken(ls, skip, at) : List<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      pt.broken_of(l, skip, at, TChoice.broken(rest, skip, 1n+at), Theme.th.broken(rest, skip, 1n+at), pt.broken(rest, skip, 1n+at))

def pt.broken_w(w: Bool, +id: U32, +ls: List<&2, TChoice.Ld>, +n: String) -> {Theme.th.broken.of(TChoice.pick.warn(w, id, ls, n)) == Theme.th.broken(ls, Theme.th.skip(w, Theme.th.blame(ls, n, 0n)), 0n) : List<&2, Nat>}:
  match w:
    case True{}:
      %Equal.sym(Maybe<&2, Nat>, TChoice.cause.go(ls, n, 0n), Theme.th.blame(ls, n, 0n), LA.pt.cause_go(ls, n, 0n)) : {TChoice.broken(ls, _, 0n) == Theme.th.broken(ls, Theme.th.blame(ls, n, 0n), 0n) : List<&2, Nat>}
      pt.broken(ls, Theme.th.blame(ls, n, 0n), 0n)
    case False{}:
      pt.broken(ls, None{}, 0n)

def Theme.theme_pick_broken(ls, n, id, w, r):
  %Equal.sym(TChoice.Pick, TChoice.pick(ls, n), TChoice.pick.warn(w, id, ls, n), LA.pt.pick_w(ls, n, id, w, r)) : {Theme.th.broken.of(_) == Theme.th.broken(ls, Theme.th.skip(w, Theme.th.blame(ls, n, 0n)), 0n) : List<&2, Nat>}
  pt.broken_w(w, id, ls, n)

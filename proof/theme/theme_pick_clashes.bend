# eukhe: the proof of LAW theme_pick_clashes

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pt.named(l: TChoice.Ld, +n: String) -> {TChoice.fine.named(l, n) == Theme.th.named(l, n) : Bool}:
  match l:
    case TChoice.Fine{nm, c}:
      {==}
    case TChoice.Broke{nm, st}:
      {==}

def pt.ffirst(ls: List<&2, TChoice.Ld>, +n: String, +at: Nat) -> {TChoice.fine.first(ls, n, at) == Theme.th.first(ls, n, at) : Maybe<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      %Equal.sym(Bool, TChoice.fine.named(l, n), Theme.th.named(l, n), pt.named(l, n)) : {TChoice.first.pick(_, at, TChoice.fine.first(rest, n, 1n+at)) == Theme.th.at.if(Theme.th.named(l, n), at, Theme.th.first(rest, n, 1n+at)) : Maybe<&2, Nat>}
      LA.pt.first_if(Theme.th.named(l, n), at, TChoice.fine.first(rest, n, 1n+at), Theme.th.first(rest, n, 1n+at), pt.ffirst(rest, n, 1n+at))

def pt.clash_if(c: Bool, w: Nat, at: Nat, -r: List<&2, TChoice.Clash>, -s: List<&2, TChoice.Clash>, e: {r == s : List<&2, TChoice.Clash>}) -> {TChoice.clash.cons(TChoice.clash.if(c, w, at), r) == List.append(&2, TChoice.Clash, Theme.th.clash.if(c, w, at), s) : List<&2, TChoice.Clash>}:
  match c:
    case True{}:
      e
    case False{}:
      Equal.cong(List<&2, TChoice.Clash>, List<&2, TChoice.Clash>, xs => TChoice.Clash{at, w} <> xs, r, s, e)

def pt.clash_of(m: Maybe<&2, Nat>, +at: Nat, -r: List<&2, TChoice.Clash>, -s: List<&2, TChoice.Clash>, e: {r == s : List<&2, TChoice.Clash>}) -> {TChoice.clash.cons(TChoice.clash.of(m, at), r) == List.append(&2, TChoice.Clash, Theme.th.clash(m, at), s) : List<&2, TChoice.Clash>}:
  match m:
    case None{}:
      e
    case Some{+w}:
      pt.clash_if(Nat.is_eq(w, at), w, at, r, s, e)

def pt.clashes(+all: List<&2, TChoice.Ld>, ls: List<&2, TChoice.Ld>, +at: Nat) -> {TChoice.clashes.go(all, ls, at) == Theme.th.clashes.go(all, ls, at) : List<&2, TChoice.Clash>}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      match l:
        case TChoice.Fine{+nm, c}:
          %Equal.sym(Maybe<&2, Nat>, TChoice.fine.first(all, nm, 0n), Theme.th.first(all, nm, 0n), pt.ffirst(all, nm, 0n)) : {TChoice.clash.cons(TChoice.clash.of(_, at), TChoice.clashes.go(all, rest, 1n+at)) == List.append(&2, TChoice.Clash, Theme.th.clash(Theme.th.first(all, nm, 0n), at), Theme.th.clashes.go(all, rest, 1n+at)) : List<&2, TChoice.Clash>}
          pt.clash_of(Theme.th.first(all, nm, 0n), at, TChoice.clashes.go(all, rest, 1n+at), Theme.th.clashes.go(all, rest, 1n+at), pt.clashes(all, rest, 1n+at))
        case TChoice.Broke{nm, st}:
          pt.clashes(all, rest, 1n+at)

def pt.clashes_go(r: TName.Res, +ls: List<&2, TChoice.Ld>, +n: String) -> {Theme.th.clashes.of(TChoice.pick.go(r, ls, n)) == TChoice.clashes(ls) : List<&2, TChoice.Clash>}:
  match r:
    case TName.Res{id, w}:
      match w:
        case True{}:
          {==}
        case False{}:
          {==}

def Theme.theme_pick_clashes(ls, n):
  Equal.trans(List<&2, TChoice.Clash>, Theme.th.clashes.of(TChoice.pick(ls, n)), TChoice.clashes(ls), Theme.th.clashes(ls), pt.clashes_go(TChoice.pick.res(ls, n), ls, n), pt.clashes(ls, ls, 0n))

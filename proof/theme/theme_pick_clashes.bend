# eukhe: the proof of LAW theme_pick_clashes

import Base
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pt.named(l: T.Ld, +n: String) -> {T.fine.named(l, n) == Theme.th.named(l, n) : Bool}:
  match l:
    case T.Fine{nm, c}:
      {==}
    case T.Broke{nm, st}:
      {==}

def pt.ffirst(ls: List<&2, T.Ld>, +n: String, +at: Nat) -> {T.fine.first(ls, n, at) == Theme.th.first(ls, n, at) : Maybe<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      %Equal.sym(Bool, T.fine.named(l, n), Theme.th.named(l, n), pt.named(l, n)) : {T.first.pick(_, at, T.fine.first(rest, n, 1n+at)) == Theme.th.at.if(Theme.th.named(l, n), at, Theme.th.first(rest, n, 1n+at)) : Maybe<&2, Nat>}
      LA.pt.first_if(Theme.th.named(l, n), at, T.fine.first(rest, n, 1n+at), Theme.th.first(rest, n, 1n+at), pt.ffirst(rest, n, 1n+at))

def pt.clash_if(c: Bool, w: Nat, at: Nat, -r: List<&2, T.Clash>, -s: List<&2, T.Clash>, e: {r == s : List<&2, T.Clash>}) -> {T.clash.cons(T.clash.if(c, w, at), r) == List.append(&2, T.Clash, Theme.th.clash.if(c, w, at), s) : List<&2, T.Clash>}:
  match c:
    case True{}:
      e
    case False{}:
      Equal.cong(List<&2, T.Clash>, List<&2, T.Clash>, xs => T.Clash{at, w} <> xs, r, s, e)

def pt.clash_of(m: Maybe<&2, Nat>, +at: Nat, -r: List<&2, T.Clash>, -s: List<&2, T.Clash>, e: {r == s : List<&2, T.Clash>}) -> {T.clash.cons(T.clash.of(m, at), r) == List.append(&2, T.Clash, Theme.th.clash(m, at), s) : List<&2, T.Clash>}:
  match m:
    case None{}:
      e
    case Some{+w}:
      pt.clash_if(Nat.is_eq(w, at), w, at, r, s, e)

def pt.clashes(+all: List<&2, T.Ld>, ls: List<&2, T.Ld>, +at: Nat) -> {T.clashes.go(all, ls, at) == Theme.th.clashes.go(all, ls, at) : List<&2, T.Clash>}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      match l:
        case T.Fine{+nm, c}:
          %Equal.sym(Maybe<&2, Nat>, T.fine.first(all, nm, 0n), Theme.th.first(all, nm, 0n), pt.ffirst(all, nm, 0n)) : {T.clash.cons(T.clash.of(_, at), T.clashes.go(all, rest, 1n+at)) == List.append(&2, T.Clash, Theme.th.clash(Theme.th.first(all, nm, 0n), at), Theme.th.clashes.go(all, rest, 1n+at)) : List<&2, T.Clash>}
          pt.clash_of(Theme.th.first(all, nm, 0n), at, T.clashes.go(all, rest, 1n+at), Theme.th.clashes.go(all, rest, 1n+at), pt.clashes(all, rest, 1n+at))
        case T.Broke{nm, st}:
          pt.clashes(all, rest, 1n+at)

def pt.clashes_go(r: T.Res, +ls: List<&2, T.Ld>, +n: String) -> {Theme.th.clashes.of(T.pick.go(r, ls, n)) == T.clashes(ls) : List<&2, T.Clash>}:
  match r:
    case T.Res{id, w}:
      match w:
        case True{}:
          {==}
        case False{}:
          {==}

def Theme.theme_pick_clashes(ls, n):
  Equal.trans(List<&2, T.Clash>, Theme.th.clashes.of(T.pick(ls, n)), T.clashes(ls), Theme.th.clashes(ls), pt.clashes_go(T.pick.res(ls, n), ls, n), pt.clashes(ls, ls, 0n))

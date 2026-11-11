# eukhe: the proof of LAW theme_pick_broken_once
# The broken list of a pick is the model's broken over the files from
# index 0, skipping the cause's index. Over the files from index at it
# holds at + i exactly when the file at i did not load and is not skipped
# (bo.mem), holds nothing below at (bo.below), every number of it is above
# any x below at (bo.above), and it rises (bo.rising).

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../laws/theme_pick.bend as ThemePick
import ./base.bend as LA
import ../theme/base.bend as LT

# Nat facts
# ---------

def bo.eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      bo.eq_refl(p)

def bo.lt_self(a: Nat) -> {Nat.is_lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      bo.lt_self(p)

def bo.lt_succ(j: Nat, a: Nat, h: {Nat.is_lt(j, a) == True{} : Bool}) -> {Nat.is_lt(j, 1n+a) == True{} : Bool}:
  match j a:
    case 0n 0n:
      LT.themes.pt.absurdF({Nat.is_lt(0n, 1n+0n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LT.themes.pt.absurdF({Nat.is_lt(1n+p, 1n+0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      bo.lt_succ(p, q, h)

def bo.lt_ne(j: Nat, a: Nat, h: {Nat.is_lt(j, a) == True{} : Bool}) -> {Nat.is_eq(a, j) == False{} : Bool}:
  match j a:
    case 0n 0n:
      LT.themes.pt.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LT.themes.pt.absurdF({Nat.is_eq(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      bo.lt_ne(p, q, h)

def bo.ne_succ(a: Nat, -p: Nat) -> {Nat.is_eq(a, 1n+Nat.add(a, p)) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      bo.ne_succ(q, p)

# The cause's index is the skipped one
# ------------------------------------

def bo.cs(m: Maybe<&2, Nat>, +i: Nat) -> {ThemePick.th.cause.at(Some{TChoice.cause.of(m)}, i) == TChoice.skip.is(m, i) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{k}:
      {==}

# Membership
# ----------

def bo.below_keep(b: Bool, +at: Nat, -r: List<&2, Nat>, +j: Nat, lt: {Nat.is_lt(j, at) == True{} : Bool}, ih: {ThemePick.th.mem(r, j) == False{} : Bool}) -> {ThemePick.th.mem(TChoice.broken.keep(b, at, r), j) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(at, j), False{}, bo.lt_ne(j, at, lt)) : {Bool.or(_, ThemePick.th.mem(r, j)) == False{} : Bool}
      ih
    case False{}:
      ih

def bo.below(ls: List<&2, TChoice.Ld>, +skip: Maybe<&2, Nat>, +at: Nat, +j: Nat, +lt: {Nat.is_lt(j, at) == True{} : Bool}) -> {ThemePick.th.mem(TChoice.broken(ls, skip, at), j) == False{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      match l:
        case TChoice.Fine{nm, c}:
          bo.below(rest, skip, 1n+at, j, bo.lt_succ(j, at, lt))
        case TChoice.Broke{nm, st}:
          bo.below_keep(Bool.not(TChoice.skip.is(skip, at)), at, TChoice.broken(rest, skip, 1n+at), j, lt, bo.below(rest, skip, 1n+at, j, bo.lt_succ(j, at, lt)))

def bo.here_keep(b: Bool, +at: Nat, -r: List<&2, Nat>, hr: {ThemePick.th.mem(r, at) == False{} : Bool}) -> {ThemePick.th.mem(TChoice.broken.keep(Bool.not(b), at, r), at) == Bool.and(True{}, Bool.not(b)) : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(at, at), True{}, bo.eq_refl(at)) : {Bool.or(_, ThemePick.th.mem(r, at)) == True{} : Bool}
      {==}

def bo.here(l: TChoice.Ld, +skip: Maybe<&2, Nat>, +at: Nat, -r: List<&2, Nat>, hr: {ThemePick.th.mem(r, at) == False{} : Bool}) -> {ThemePick.th.mem(TChoice.broken.of(l, skip, at, r), at) == Bool.and(ThemePick.th.broke.of(Some{l}), Bool.not(TChoice.skip.is(skip, at))) : Bool}:
  match l:
    case TChoice.Fine{nm, c}:
      hr
    case TChoice.Broke{nm, st}:
      bo.here_keep(TChoice.skip.is(skip, at), at, r, hr)

def bo.there_keep(b: Bool, +at: Nat, -r: List<&2, Nat>, +j: Nat, -x: Bool, hne: {Nat.is_eq(at, j) == False{} : Bool}, ih: {ThemePick.th.mem(r, j) == x : Bool}) -> {ThemePick.th.mem(TChoice.broken.keep(b, at, r), j) == x : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(at, j), False{}, hne) : {Bool.or(_, ThemePick.th.mem(r, j)) == x : Bool}
      ih
    case False{}:
      ih

def bo.there(l: TChoice.Ld, +skip: Maybe<&2, Nat>, +at: Nat, -r: List<&2, Nat>, +j: Nat, -x: Bool, hne: {Nat.is_eq(at, j) == False{} : Bool}, ih: {ThemePick.th.mem(r, j) == x : Bool}) -> {ThemePick.th.mem(TChoice.broken.of(l, skip, at, r), j) == x : Bool}:
  match l:
    case TChoice.Fine{nm, c}:
      ih
    case TChoice.Broke{nm, st}:
      bo.there_keep(Bool.not(TChoice.skip.is(skip, at)), at, r, j, x, hne, ih)

def bo.mem(ls: List<&2, TChoice.Ld>, +skip: Maybe<&2, Nat>, +at: Nat, i: Nat) -> {ThemePick.th.mem(TChoice.broken(ls, skip, at), Nat.add(at, i)) == Bool.and(ThemePick.th.broke.at(ls, i), Bool.not(TChoice.skip.is(skip, Nat.add(at, i)))) : Bool}:
  match ls i:
    case Nil{} q:
      {==}
    case Con{+l, +rest} 0n:
      %LA.pk.add0(at) : {ThemePick.th.mem(TChoice.broken.of(l, skip, at, TChoice.broken(rest, skip, 1n+at)), _) == Bool.and(ThemePick.th.broke.of(Some{l}), Bool.not(TChoice.skip.is(skip, _))) : Bool}
      bo.here(l, skip, at, TChoice.broken(rest, skip, 1n+at), bo.below(rest, skip, 1n+at, at, bo.lt_self(at)))
    case Con{+l, +rest} 1n++p:
      %Equal.sym(Nat, Nat.add(at, 1n+p), 1n+Nat.add(at, p), LA.pk.add_succ(at, p)) : {ThemePick.th.mem(TChoice.broken.of(l, skip, at, TChoice.broken(rest, skip, 1n+at)), _) == Bool.and(ThemePick.th.broke.at(rest, p), Bool.not(TChoice.skip.is(skip, _))) : Bool}
      bo.there(l, skip, at, TChoice.broken(rest, skip, 1n+at), 1n+Nat.add(at, p), Bool.and(ThemePick.th.broke.at(rest, p), Bool.not(TChoice.skip.is(skip, 1n+Nat.add(at, p)))), bo.ne_succ(at, p), bo.mem(rest, skip, 1n+at, p))

# Order
# -----

def bo.above_keep(b: Bool, +a: Nat, -r: List<&2, Nat>, +x: Nat, lt: {Nat.is_lt(x, a) == True{} : Bool}, ih: {ThemePick.th.above(r, x) == True{} : Bool}) -> {ThemePick.th.above(TChoice.broken.keep(b, a, r), x) == True{} : Bool}:
  match b:
    case True{}:
      lt
    case False{}:
      ih

def bo.above(ls: List<&2, TChoice.Ld>, +skip: Maybe<&2, Nat>, +a: Nat, +x: Nat, +lt: {Nat.is_lt(x, a) == True{} : Bool}) -> {ThemePick.th.above(TChoice.broken(ls, skip, a), x) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      match l:
        case TChoice.Fine{nm, c}:
          bo.above(rest, skip, 1n+a, x, bo.lt_succ(x, a, lt))
        case TChoice.Broke{nm, st}:
          bo.above_keep(Bool.not(TChoice.skip.is(skip, a)), a, TChoice.broken(rest, skip, 1n+a), x, lt, bo.above(rest, skip, 1n+a, x, bo.lt_succ(x, a, lt)))

def bo.rising_keep(b: Bool, +at: Nat, +r: List<&2, Nat>, ha: {ThemePick.th.above(r, at) == True{} : Bool}, ih: {ThemePick.th.rising(r) == True{} : Bool}) -> {ThemePick.th.rising(TChoice.broken.keep(b, at, r)) == True{} : Bool}:
  match b:
    case True{}:
      LT.themes.pt.and_t(ThemePick.th.above(r, at), ThemePick.th.rising(r), ha, ih)
    case False{}:
      ih

def bo.rising(ls: List<&2, TChoice.Ld>, +skip: Maybe<&2, Nat>, +at: Nat) -> {ThemePick.th.rising(TChoice.broken(ls, skip, at)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      match l:
        case TChoice.Fine{nm, c}:
          bo.rising(rest, skip, 1n+at)
        case TChoice.Broke{nm, st}:
          bo.rising_keep(Bool.not(TChoice.skip.is(skip, at)), at, TChoice.broken(rest, skip, 1n+at), bo.above(rest, skip, 1n+at, at, bo.lt_self(at)), bo.rising(rest, skip, 1n+at))

# The law
# -------

def bo.go(r: TName.Res, +ls: List<&2, TChoice.Ld>, +n: String, +i: Nat)
  -> {ThemePick.th.mem(ThemePick.th.broken.of(TChoice.pick.go(r, ls, n)), i) == Bool.and(ThemePick.th.broke.at(ls, i), Bool.not(ThemePick.th.cause.at(ThemePick.th.cause(TChoice.pick.go(r, ls, n)), i))) : Bool} & {ThemePick.th.rising(ThemePick.th.broken.of(TChoice.pick.go(r, ls, n))) == True{} : Bool}:
  match r:
    case TName.Res{id, w}:
      match w:
        case True{}:
          +m = TChoice.cause.go(ls, n, 0n)
          %Equal.sym(Bool, ThemePick.th.cause.at(Some{TChoice.cause.of(m)}, i), TChoice.skip.is(m, i), bo.cs(m, i)) : {ThemePick.th.mem(TChoice.broken(ls, m, 0n), i) == Bool.and(ThemePick.th.broke.at(ls, i), Bool.not(_)) : Bool} & {ThemePick.th.rising(TChoice.broken(ls, m, 0n)) == True{} : Bool}
          (bo.mem(ls, m, 0n, i), bo.rising(ls, m, 0n))
        case False{}:
          (bo.mem(ls, None{}, 0n, i), bo.rising(ls, None{}, 0n))

def ThemePick.theme_pick_broken_once(ls, n, i):
  bo.go(TChoice.pick.res(ls, n), ls, n, i)

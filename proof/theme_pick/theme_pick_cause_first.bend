# eukhe: the proof of LAW theme_pick_cause_first: a pick that warns takes
# its cause from the search for the first file that blames the name
# (LA.pk.blame_first), one that does not has none

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../laws/theme_pick.bend as ThemePick
import ./base.bend as LA

def pcf.go(r: TName.Res, +ls: List<&2, TChoice.Ld>, +n: String, +k: Nat, hm: {TChoice.cause.go(ls, n, 0n) == Some{k} : Maybe<&2, Nat>})
  -> {ThemePick.th.cause(TChoice.pick.go(r, ls, n)) == ThemePick.th.when(ThemePick.th.warned(TChoice.pick.go(r, ls, n)), TChoice.FailedAt{k}) : Maybe<&2, TChoice.Cause>}:
  match r:
    case TName.Res{id, w}:
      match w:
        case True{}:
          %Equal.sym(Maybe<&2, Nat>, TChoice.cause.go(ls, n, 0n), Some{k}, hm) : {Some{TChoice.cause.of(_)} == Some{TChoice.FailedAt{k}} : Maybe<&2, TChoice.Cause>}
          {==}
        case False{}:
          {==}

def pcf.first(+pre: List<&2, TChoice.Ld>, +x: TChoice.Ld, +post: List<&2, TChoice.Ld>, +n: String, no: {ThemePick.th.none.blame(pre, n) == True{} : Bool}, bl: {ThemePick.th.blames(x, n) == True{} : Bool})
  -> {ThemePick.th.cause(TChoice.pick(List.append(&2, TChoice.Ld, pre, x <> post), n)) == ThemePick.th.when(ThemePick.th.warned(TChoice.pick(List.append(&2, TChoice.Ld, pre, x <> post), n)), TChoice.FailedAt{List.length(&2, TChoice.Ld, pre)}) : Maybe<&2, TChoice.Cause>}:
  +l = List.append(&2, TChoice.Ld, pre, x <> post)
  +len = List.length(&2, TChoice.Ld, pre)
  +hb = LA.pk.blame_first(pre, x, post, n, 0n, no, bl)
  +hz = Equal.cong(Nat, Maybe<&2, Nat>, y => Some{y}, Nat.add(len, 0n), len, Equal.sym(Nat, len, Nat.add(len, 0n), LA.pk.add0(len)))
  pcf.go(TChoice.pick.res(l, n), l, n, len, Equal.trans(Maybe<&2, Nat>, TChoice.cause.go(l, n, 0n), Some{Nat.add(len, 0n)}, Some{len}, hb, hz))

def ThemePick.theme_pick_cause_first(pre, x, post, n, no, bl):
  pcf.first(pre, x, post, n, no, bl)

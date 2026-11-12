# eukhe: the proof of LAW theme_pick_cause_none: no file blames the name,
# so the search for one finds none (LA.pk.blame_none): a pick that warns
# has the cause "no theme", one that does not has none

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../laws/theme_pick.bend as ThemePick
import ./base.bend as LA

def pcn.go(r: TName.Res, +ls: List<&2, TChoice.Ld>, +n: String, hm: {TChoice.cause.go(ls, n, 0n) == None{} : Maybe<&2, Nat>})
  -> {ThemePick.th.cause(TChoice.pick.go(r, ls, n)) == ThemePick.th.when(ThemePick.th.warned(TChoice.pick.go(r, ls, n)), TChoice.NoTheme{}) : Maybe<&2, TChoice.Cause>}:
  match r:
    case TName.Res{id, w}:
      match w:
        case True{}:
          %Equal.sym(Maybe<&2, Nat>, TChoice.cause.go(ls, n, 0n), None{}, hm) : {Some{TChoice.cause.of(_)} == Some{TChoice.NoTheme{}} : Maybe<&2, TChoice.Cause>}
          {==}
        case False{}:
          {==}

def ThemePick.theme_pick_cause_none(ls, n, no):
  pcn.go(TChoice.pick.res(ls, n), ls, n, LA.pk.blame_none(ls, n, 0n, no))

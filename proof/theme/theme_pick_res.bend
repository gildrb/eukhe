# eukhe: the proof of LAW theme_pick_res

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pt.res_go(r: TName.Res, +ls: List<&2, TChoice.Ld>, +n: String) -> {Theme.th.res(TChoice.pick.go(r, ls, n)) == r : TName.Res}:
  match r:
    case TName.Res{id, w}:
      match w:
        case True{}:
          {==}
        case False{}:
          {==}

def Theme.theme_pick_res(ls, n):
  Equal.trans(TName.Res, Theme.th.res(TChoice.pick(ls, n)), TChoice.pick.res(ls, n), Theme.th.pick(ls, n), pt.res_go(TChoice.pick.res(ls, n), ls, n), LA.pt.pickres(ls, n))

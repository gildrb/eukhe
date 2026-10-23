# eukhe: the proof of LAW theme_pick_res

import Base
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pt.res_go(r: T.Res, +ls: List<&2, T.Ld>, +n: String) -> {Theme.th.res(T.pick.go(r, ls, n)) == r : T.Res}:
  match r:
    case T.Res{id, w}:
      match w:
        case True{}:
          {==}
        case False{}:
          {==}

def Theme.theme_pick_res(ls, n):
  Equal.trans(T.Res, Theme.th.res(T.pick(ls, n)), T.pick.res(ls, n), Theme.th.pick(ls, n), pt.res_go(T.pick.res(ls, n), ls, n), LA.pt.pickres(ls, n))

# eukhe: the proof of LAW theme_pick_quiet

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.theme_pick_quiet(ls, n, id, w):
  %Equal.sym(T.Pick, T.pick(ls, n), T.pick.warn(False{}, id, ls, n), LA.pt.pick_w(ls, n, id, False{}, w)) : {Laws.th.cause(_) == None{} : Maybe<&2, T.Cause>}
  {==}

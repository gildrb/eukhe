# eukhe: the proof of LAW theme_pick_quiet

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def Theme.theme_pick_quiet(ls, n, id, w):
  %Equal.sym(TChoice.Pick, TChoice.pick(ls, n), TChoice.pick.warn(False{}, id, ls, n), LA.pt.pick_w(ls, n, id, False{}, w)) : {Theme.th.cause(_) == None{} : Maybe<&2, TChoice.Cause>}
  {==}

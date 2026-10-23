# eukhe: the proof of LAW theme_entry_invalid

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws

def Laws.theme_entry_invalid(vars, k, t, j, why, h):
  %Equal.sym(T.Got, T.chase(vars, j), T.Miss{why}, h) : {T.entry.got(k, t, _) == T.Bad{T.InColor{k, why}} : T.EntR}
  {==}

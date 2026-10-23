# eukhe: the proof of LAW theme_entry_color

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws

def Laws.theme_entry_color(vars, k, t, j, v, h):
  %Equal.sym(T.Got, T.chase(vars, j), T.Hit{v}, h) : {T.entry.got(k, t, _) == T.Good{T.Ent{t, v}} : T.EntR}
  {==}

# eukhe: the proof of LAW theme_read_page

import Base
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def Theme.theme_read_page(nm, vars, cols, j, cd, io, why, ok, all, bad):
  +gs = Theme.th.goods(vars, cols)
  +want = {T.Failed{T.InExport{T.OnPage{}, why}} : T.Read}
  %Equal.sym(T.Read, T.read(T.RFile{nm, vars, cols, Some{j}, cd, io}), T.read.end(nm, gs, T.surf(T.index(vars), T.OnPage{}, Some{j}), T.surf(T.index(vars), T.OnCard{}, cd), T.surf(T.index(vars), T.OnInfo{}, io)), LA.pt.read_end(nm, vars, cols, Some{j}, cd, io, ok, all)) : {_ == want : T.Read}
  %Equal.sym(T.Got, T.chase(vars, j), T.Miss{why}, bad) : {T.read.end(nm, gs, T.surf.got(T.OnPage{}, _), T.surf(T.index(vars), T.OnCard{}, cd), T.surf(T.index(vars), T.OnInfo{}, io)) == want : T.Read}
  {==}

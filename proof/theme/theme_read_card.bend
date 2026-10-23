# eukhe: the proof of LAW theme_read_card

import Base
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def Theme.theme_read_card(nm, vars, cols, pg, j, io, why, ok, all, fine, bad):
  +gs = Theme.th.goods(vars, cols)
  +want = {T.Failed{T.InExport{T.OnCard{}, why}} : T.Read}
  %Equal.sym(T.Read, T.read(T.RFile{nm, vars, cols, pg, Some{j}, io}), T.read.end(nm, gs, T.surf(T.index(vars), T.OnPage{}, pg), T.surf(T.index(vars), T.OnCard{}, Some{j}), T.surf(T.index(vars), T.OnInfo{}, io)), LA.pt.read_end(nm, vars, cols, pg, Some{j}, io, ok, all)) : {_ == want : T.Read}
  %Equal.sym(T.Bg, T.surf(T.index(vars), T.OnPage{}, pg), T.BgOk{Theme.th.bgv(vars, pg)}, LA.pt.surf_fine(vars, T.OnPage{}, pg, fine)) : {T.read.end(nm, gs, _, T.surf(T.index(vars), T.OnCard{}, Some{j}), T.surf(T.index(vars), T.OnInfo{}, io)) == want : T.Read}
  %Equal.sym(T.Got, T.chase(vars, j), T.Miss{why}, bad) : {T.read.end(nm, gs, T.BgOk{Theme.th.bgv(vars, pg)}, T.surf.got(T.OnCard{}, _), T.surf(T.index(vars), T.OnInfo{}, io)) == want : T.Read}
  {==}

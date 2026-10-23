# eukhe: the proof of LAW theme_read_info

import Base
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def Theme.theme_read_info(nm, vars, cols, pg, cd, j, why, ok, all, fine1, fine2, bad):
  +gs = Theme.th.goods(vars, cols)
  +want = {T.Failed{T.InExport{T.OnInfo{}, why}} : T.Read}
  %Equal.sym(T.Read, T.read(T.RFile{nm, vars, cols, pg, cd, Some{j}}), T.read.end(nm, gs, T.surf(T.index(vars), T.OnPage{}, pg), T.surf(T.index(vars), T.OnCard{}, cd), T.surf(T.index(vars), T.OnInfo{}, Some{j})), LA.pt.read_end(nm, vars, cols, pg, cd, Some{j}, ok, all)) : {_ == want : T.Read}
  %Equal.sym(T.Bg, T.surf(T.index(vars), T.OnPage{}, pg), T.BgOk{Theme.th.bgv(vars, pg)}, LA.pt.surf_fine(vars, T.OnPage{}, pg, fine1)) : {T.read.end(nm, gs, _, T.surf(T.index(vars), T.OnCard{}, cd), T.surf(T.index(vars), T.OnInfo{}, Some{j})) == want : T.Read}
  %Equal.sym(T.Bg, T.surf(T.index(vars), T.OnCard{}, cd), T.BgOk{Theme.th.bgv(vars, cd)}, LA.pt.surf_fine(vars, T.OnCard{}, cd, fine2)) : {T.read.end(nm, gs, T.BgOk{Theme.th.bgv(vars, pg)}, _, T.surf(T.index(vars), T.OnInfo{}, Some{j})) == want : T.Read}
  %Equal.sym(T.Got, T.chase(vars, j), T.Miss{why}, bad) : {T.read.end(nm, gs, T.BgOk{Theme.th.bgv(vars, pg)}, T.BgOk{Theme.th.bgv(vars, cd)}, T.surf.got(T.OnInfo{}, _)) == want : T.Read}
  {==}

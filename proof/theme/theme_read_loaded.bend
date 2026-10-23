# eukhe: the proof of LAW theme_read_loaded

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.theme_read_loaded(nm, vars, cols, pg, cd, io, ok, all, fine1, fine2, fine3):
  +gs = Laws.th.goods(vars, cols)
  +want = {T.Loaded{T.Th{nm, gs, Laws.th.bgv(vars, pg), Laws.th.bgv(vars, cd), Laws.th.bgv(vars, io)}} : T.Read}
  %Equal.sym(T.Read, T.read(T.RFile{nm, vars, cols, pg, cd, io}), T.read.end(nm, gs, T.surf(T.index(vars), T.OnPage{}, pg), T.surf(T.index(vars), T.OnCard{}, cd), T.surf(T.index(vars), T.OnInfo{}, io)), LA.pt.read_end(nm, vars, cols, pg, cd, io, ok, all)) : {_ == want : T.Read}
  %Equal.sym(T.Bg, T.surf(T.index(vars), T.OnPage{}, pg), T.BgOk{Laws.th.bgv(vars, pg)}, LA.pt.surf_fine(vars, T.OnPage{}, pg, fine1)) : {T.read.end(nm, gs, _, T.surf(T.index(vars), T.OnCard{}, cd), T.surf(T.index(vars), T.OnInfo{}, io)) == want : T.Read}
  %Equal.sym(T.Bg, T.surf(T.index(vars), T.OnCard{}, cd), T.BgOk{Laws.th.bgv(vars, cd)}, LA.pt.surf_fine(vars, T.OnCard{}, cd, fine2)) : {T.read.end(nm, gs, T.BgOk{Laws.th.bgv(vars, pg)}, _, T.surf(T.index(vars), T.OnInfo{}, io)) == want : T.Read}
  %Equal.sym(T.Bg, T.surf(T.index(vars), T.OnInfo{}, io), T.BgOk{Laws.th.bgv(vars, io)}, LA.pt.surf_fine(vars, T.OnInfo{}, io, fine3)) : {T.read.end(nm, gs, T.BgOk{Laws.th.bgv(vars, pg)}, T.BgOk{Laws.th.bgv(vars, cd)}, _) == want : T.Read}
  {==}

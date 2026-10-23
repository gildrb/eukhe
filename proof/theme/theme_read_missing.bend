# eukhe: the proof of LAW theme_read_missing

import Base
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def Theme.theme_read_missing(nm, vars, cols, pg, cd, io, t, ts, ok, miss):
  +gs = Theme.th.goods(vars, cols)
  +mt = Equal.trans(List<&2, U32>, T.missing(gs), Theme.th.absent(gs), t <> ts, LA.pt.missing_absent(gs), miss)
  %Equal.sym(T.Ents, T.ents(T.index(vars), cols), T.All{gs}, LA.pt.ents_all(vars, cols, ok)) : {T.read.cols(nm, T.index(vars), _, pg, cd, io) == T.Failed{T.Missing{t <> ts}} : T.Read}
  %Equal.sym(List<&2, U32>, T.missing(gs), t <> ts, mt) : {T.read.full(nm, T.index(vars), gs, _, pg, cd, io) == T.Failed{T.Missing{t <> ts}} : T.Read}
  {==}

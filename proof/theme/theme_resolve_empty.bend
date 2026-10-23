# eukhe: the proof of LAW theme_resolve_empty

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws

def theme_resolve_empty(src: List<&2, T.Cand>) -> {T.resolve.name(src, "") == T.Res{T.dflt(), False{}} : T.Res}:
  {==}

# (T1) Themes

def Laws.theme_resolve_empty(src):
  theme_resolve_empty(src)

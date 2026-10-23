# eukhe: the proof of LAW theme_resolve_empty

import Base
import ../../bend/theme/name.bend as TName
import ../../laws/theme.bend as Theme

def theme_resolve_empty(src: List<&2, TName.Cand>) -> {TName.resolve.name(src, "") == TName.Res{TName.dflt(), False{}} : TName.Res}:
  {==}

# (T1) Themes

def Theme.theme_resolve_empty(src):
  theme_resolve_empty(src)

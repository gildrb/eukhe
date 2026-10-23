# eukhe: the proof of LAW theme_resolve_missing

import Base
import ../../bend/theme/name.bend as TName
import ../../laws/theme.bend as Theme
import ./base.bend as LA

# Resolution
# ----------

# a scan of candidates none of which resolves n ends at the default theme,
# with a warning
def pt.find_miss(+src: List<&2, TName.Cand>, +n: String, +miss: {TName.hit(src, n) == False{} : Bool}) -> {TName.find(src, n) == TName.Res{TName.dflt(), True{}} : TName.Res}:
  match src:
    case Nil{}:
      {==}
    case Con{TName.Cand{nm, v, id}, rest}:
      +here = LA.pt.or_false_l(TName.names(TName.Cand{nm, v, id}, n), TName.hit(rest, n), miss)
      %Equal.sym(Bool, TName.names(TName.Cand{nm, v, id}, n), False{}, here) : {TName.find.pick(_, id, TName.find(rest, n)) == TName.Res{TName.dflt(), True{}} : TName.Res}
      pt.find_miss(rest, n, LA.themes.pt.or_false_r(TName.names(TName.Cand{nm, v, id}, n), TName.hit(rest, n), miss))

def theme_resolve_missing(+src: List<&2, TName.Cand>, +n: String, ne: {String.is_empty(n) == False{} : Bool}, miss: {TName.hit(src, n) == False{} : Bool})
  -> {TName.resolve.name(src, n) == TName.Res{TName.dflt(), True{}} : TName.Res}:
  %Equal.sym(Bool, String.is_empty(n), False{}, ne) : {TName.resolve.name.pick(_, src, n) == TName.Res{TName.dflt(), True{}} : TName.Res}
  pt.find_miss(src, n, miss)

def Theme.theme_resolve_missing(src, n, ne, miss):
  theme_resolve_missing(src, n, ne, miss)

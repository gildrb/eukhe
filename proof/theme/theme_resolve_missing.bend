# eukhe: the proof of LAW theme_resolve_missing

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws
import ./base.bend as LA

# Resolution
# ----------

# a scan of candidates none of which resolves n ends at the default theme,
# with a warning
def pt.find_miss(+src: List<&2, T.Cand>, +n: String, +miss: {T.hit(src, n) == False{} : Bool}) -> {T.find(src, n) == T.Res{T.dflt(), True{}} : T.Res}:
  match src:
    case Nil{}:
      {==}
    case Con{T.Cand{nm, v, id}, rest}:
      +here = LA.pt.or_false_l(T.names(T.Cand{nm, v, id}, n), T.hit(rest, n), miss)
      %Equal.sym(Bool, T.names(T.Cand{nm, v, id}, n), False{}, here) : {T.find.pick(_, id, T.find(rest, n)) == T.Res{T.dflt(), True{}} : T.Res}
      pt.find_miss(rest, n, LA.themes.pt.or_false_r(T.names(T.Cand{nm, v, id}, n), T.hit(rest, n), miss))

def theme_resolve_missing(+src: List<&2, T.Cand>, +n: String, ne: {String.is_empty(n) == False{} : Bool}, miss: {T.hit(src, n) == False{} : Bool})
  -> {T.resolve.name(src, n) == T.Res{T.dflt(), True{}} : T.Res}:
  %Equal.sym(Bool, String.is_empty(n), False{}, ne) : {T.resolve.name.pick(_, src, n) == T.Res{T.dflt(), True{}} : T.Res}
  pt.find_miss(src, n, miss)

def Laws.theme_resolve_missing(src, n, ne, miss):
  theme_resolve_missing(src, n, ne, miss)

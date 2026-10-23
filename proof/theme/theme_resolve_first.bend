# eukhe: the proof of LAW theme_resolve_first

import Base
import ../../bend/theme/name.bend as TName
import ../../laws/theme.bend as Theme
import ./base.bend as LA

# a scan whose candidates before c do not resolve n finds c
def pt.find_first(+pre: List<&2, TName.Cand>, +nm: String, +id: U32, +post: List<&2, TName.Cand>, +n: String, +miss: {TName.hit(pre, n) == False{} : Bool}, same: {String.eq(nm, n) == True{} : Bool})
  -> {TName.find(List.append(&2, TName.Cand, pre, TName.Cand{nm, True{}, id} <> post), n) == TName.Res{id, False{}} : TName.Res}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, String.eq(nm, n), True{}, same) : {TName.find.pick(Bool.and(True{}, _), id, TName.find(post, n)) == TName.Res{id, False{}} : TName.Res}
      {==}
    case Con{TName.Cand{pn, pv, pid}, rest}:
      +here = LA.pt.or_false_l(TName.names(TName.Cand{pn, pv, pid}, n), TName.hit(rest, n), miss)
      %Equal.sym(Bool, TName.names(TName.Cand{pn, pv, pid}, n), False{}, here) : {TName.find.pick(_, pid, TName.find(List.append(&2, TName.Cand, rest, TName.Cand{nm, True{}, id} <> post), n)) == TName.Res{id, False{}} : TName.Res}
      pt.find_first(rest, nm, id, post, n, LA.themes.pt.or_false_r(TName.names(TName.Cand{pn, pv, pid}, n), TName.hit(rest, n), miss), same)

def theme_resolve_first(+pre: List<&2, TName.Cand>, +nm: String, +id: U32, +post: List<&2, TName.Cand>, +n: String, ne: {String.is_empty(n) == False{} : Bool}, miss: {TName.hit(pre, n) == False{} : Bool}, same: {String.eq(nm, n) == True{} : Bool})
  -> {TName.resolve.name(List.append(&2, TName.Cand, pre, TName.Cand{nm, True{}, id} <> post), n) == TName.Res{id, False{}} : TName.Res}:
  %Equal.sym(Bool, String.is_empty(n), False{}, ne) : {TName.resolve.name.pick(_, List.append(&2, TName.Cand, pre, TName.Cand{nm, True{}, id} <> post), n) == TName.Res{id, False{}} : TName.Res}
  pt.find_first(pre, nm, id, post, n, miss, same)

def Theme.theme_resolve_first(pre, nm, id, post, n, ne, miss, same):
  theme_resolve_first(pre, nm, id, post, n, ne, miss, same)

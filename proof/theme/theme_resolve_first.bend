# eukhe: the proof of LAW theme_resolve_first

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws
import ./base.bend as LA

# a scan whose candidates before c do not resolve n finds c
def pt.find_first(+pre: List<&2, T.Cand>, +nm: String, +id: U32, +post: List<&2, T.Cand>, +n: String, +miss: {T.hit(pre, n) == False{} : Bool}, same: {String.eq(nm, n) == True{} : Bool})
  -> {T.find(List.append(&2, T.Cand, pre, T.Cand{nm, True{}, id} <> post), n) == T.Res{id, False{}} : T.Res}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, String.eq(nm, n), True{}, same) : {T.find.pick(Bool.and(True{}, _), id, T.find(post, n)) == T.Res{id, False{}} : T.Res}
      {==}
    case Con{T.Cand{pn, pv, pid}, rest}:
      +here = LA.pt.or_false_l(T.names(T.Cand{pn, pv, pid}, n), T.hit(rest, n), miss)
      %Equal.sym(Bool, T.names(T.Cand{pn, pv, pid}, n), False{}, here) : {T.find.pick(_, pid, T.find(List.append(&2, T.Cand, rest, T.Cand{nm, True{}, id} <> post), n)) == T.Res{id, False{}} : T.Res}
      pt.find_first(rest, nm, id, post, n, LA.themes.pt.or_false_r(T.names(T.Cand{pn, pv, pid}, n), T.hit(rest, n), miss), same)

def theme_resolve_first(+pre: List<&2, T.Cand>, +nm: String, +id: U32, +post: List<&2, T.Cand>, +n: String, ne: {String.is_empty(n) == False{} : Bool}, miss: {T.hit(pre, n) == False{} : Bool}, same: {String.eq(nm, n) == True{} : Bool})
  -> {T.resolve.name(List.append(&2, T.Cand, pre, T.Cand{nm, True{}, id} <> post), n) == T.Res{id, False{}} : T.Res}:
  %Equal.sym(Bool, String.is_empty(n), False{}, ne) : {T.resolve.name.pick(_, List.append(&2, T.Cand, pre, T.Cand{nm, True{}, id} <> post), n) == T.Res{id, False{}} : T.Res}
  pt.find_first(pre, nm, id, post, n, miss, same)

def Laws.theme_resolve_first(pre, nm, id, post, n, ne, miss, same):
  theme_resolve_first(pre, nm, id, post, n, ne, miss, same)

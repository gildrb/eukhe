# eukhe: the proof of LAW theme_hit_found: induction on the candidates
# before it; the valid candidate named n makes hit true wherever it is

import Base
import ../../bend/theme/name.bend as TName
import ../../laws/theme_pick.bend as ThemePick

def hf.or_true(x: Bool, -y: Bool, h: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      h

def hf.found(pre: List<&2, TName.Cand>, +nm: String, +id: U32, +post: List<&2, TName.Cand>, +n: String, same: {String.eq(nm, n) == True{} : Bool}) -> {TName.hit(List.append(&2, TName.Cand, pre, TName.Cand{nm, True{}, id} <> post), n) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, String.eq(nm, n), True{}, same) : {Bool.or(Bool.and(True{}, _), TName.hit(post, n)) == True{} : Bool}
      {==}
    case Con{c, rest}:
      hf.or_true(TName.names(c, n), TName.hit(List.append(&2, TName.Cand, rest, TName.Cand{nm, True{}, id} <> post), n), hf.found(rest, nm, id, post, n, same))

def ThemePick.theme_hit_found(pre, nm, id, post, n, same):
  hf.found(pre, nm, id, post, n, same)

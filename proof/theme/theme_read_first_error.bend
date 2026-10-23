# eukhe: the proof of LAW theme_read_first_error

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pt.cons_stuck(r: T.EntR, -f: T.Fault, hg: {Laws.th.good(r) == True{} : Bool}) -> {T.ents.cons(r, T.Stuck{f}) == T.Stuck{f} : T.Ents}:
  match r:
    case T.Good{e}:
      {==}
    case T.Bad{x}:
      LA.themes.pt.absurdF({T.ents.cons(T.Bad{x}, T.Stuck{f}) == T.Stuck{f} : T.Ents}, hg)

def pt.ents_first(+vars: List<&2, T.Var>, +pre: List<&2, T.REnt>, +e: T.REnt, +post: List<&2, T.REnt>, +f: T.Fault, +ok: {Laws.th.clean(vars, pre) == True{} : Bool}, +bad: {T.entry(vars, e) == T.Bad{f} : T.EntR})
  -> {T.ents(T.index(vars), List.append(&2, T.REnt, pre, e <> post)) == T.Stuck{f} : T.Ents}:
  match pre:
    case Nil{}:
      %Equal.sym(T.EntR, T.entry(vars, e), T.Bad{f}, bad) : {T.ents.cons(_, T.ents(T.index(vars), post)) == T.Stuck{f} : T.Ents}
      {==}
    case Con{+x, rest}:
      +hg = LA.themes.pt.and_l(Laws.th.good(T.entry(vars, x)), Laws.th.clean(vars, rest), ok)
      +ih = pt.ents_first(vars, rest, e, post, f, LA.themes.pt.and_r(Laws.th.good(T.entry(vars, x)), Laws.th.clean(vars, rest), ok), bad)
      %Equal.sym(T.Ents, T.ents(T.index(vars), List.append(&2, T.REnt, rest, e <> post)), T.Stuck{f}, ih) : {T.ents.cons(T.entry(vars, x), _) == T.Stuck{f} : T.Ents}
      pt.cons_stuck(T.entry(vars, x), f, hg)

def Laws.theme_read_first_error(nm, vars, pre, e, post, pg, cd, io, f, ok, bad):
  %Equal.sym(T.Ents, T.ents(T.index(vars), List.append(&2, T.REnt, pre, e <> post)), T.Stuck{f}, pt.ents_first(vars, pre, e, post, f, ok, bad)) : {T.read.cols(nm, T.index(vars), _, pg, cd, io) == T.Failed{f} : T.Read}
  {==}

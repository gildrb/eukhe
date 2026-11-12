# eukhe: the proof of LAW tokens_ascends_sound
# Induction on the steps before the pair: ascends.from compares each value
# with the one before it, so the pair's comparison is a conjunct.

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

def tas.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def tas.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : tas.BD(_, A, Unit)
  Unit{}

def tas.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      tas.absurdF({False{} == True{} : Bool}, h)

def tas.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      tas.absurdF({b == True{} : Bool}, h)

def tas.from(+pre: List<&2, Tk.Step>, +u: U32, -n: String, +v: U32, -k: String, +w: U32, -post: List<&2, Tk.Step>, ok: {Tk.ascends.from(List.append(&2, Tk.Step, pre, Tk.Step{n, v} <> Tk.Step{k, w} <> post), u) == True{} : Bool}) -> {U32.is_lt(v, w) == True{} : Bool}:
  match pre:
    case Nil{}:
      tas.and_l(U32.is_lt(v, w), Tk.ascends.from(post, w), tas.and_r(U32.is_lt(u, v), Tk.ascends.from(Tk.Step{k, w} <> post, v), ok))
    case Con{s, rest}:
      match s:
        case Tk.Step{m, +x}:
          tas.from(rest, x, n, v, k, w, post, tas.and_r(U32.is_lt(u, x), Tk.ascends.from(List.append(&2, Tk.Step, rest, Tk.Step{n, v} <> Tk.Step{k, w} <> post), x), ok))

def Tokens.tokens_ascends_sound(pre, n, v, k, w, post, ok):
  match pre:
    case Nil{}:
      tas.and_l(U32.is_lt(v, w), Tk.ascends.from(post, w), ok)
    case Con{s, rest}:
      match s:
        case Tk.Step{m, +x}:
          tas.from(rest, x, n, v, k, w, post, ok)

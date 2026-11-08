# eukhe: the proof of LAW tokens_legible

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

# ---- tokens ----

# proof_tokens: the T2 laws of the token
# model in bend/tokens.bend.
#
# The tables are constants, so each claim about them computes: the
# lookup of every tone in each mode, the readable test of the pair list
# in each mode (bend/color.bend's exact contrast), and the ascent of each
# scale. A pair taken from the list (pairs = pre ++ [p] ++ post) is
# readable because the whole list is: `pt.pick` walks pre.

# Logic
# -----

def tokens.pt.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def tokens.pt.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : tokens.pt.BD(_, A, Unit)
  Unit{}

def tokens.pt.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      tokens.pt.absurdF({False{} == True{} : Bool}, h)

def tokens.pt.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      tokens.pt.absurdF({b == True{} : Bool}, h)

# Legibility
# ----------

# every pair of the list is readable, in each mode
def pt.all_readable(m: Tk.Mode) -> {Tk.readable.all(m, Tk.pairs()) == True{} : Bool}:
  match m:
    case Tk.Light{}:
      {==}
    case Tk.Dark{}:
      {==}

# a pair of a readable list is readable
def tokens.pt.pick(+m: Tk.Mode, +pre: List<&2, Tk.Ink>, +p: Tk.Ink, +post: List<&2, Tk.Ink>, h: {Tk.readable.all(m, List.append(&2, Tk.Ink, pre, p <> post)) == True{} : Bool}) -> {Tk.readable(m, p) == True{} : Bool}:
  match pre:
    case Nil{}:
      tokens.pt.and_l(Tk.readable(m, p), Tk.readable.all(m, post), h)
    case Con{+q, +rest}:
      tokens.pt.pick(m, rest, p, post, tokens.pt.and_r(Tk.readable(m, q), Tk.readable.all(m, List.append(&2, Tk.Ink, rest, p <> post)), h))

# the split list is the pair list, which is readable
def pt.whole(+m: Tk.Mode, -pre: List<&2, Tk.Ink>, -p: Tk.Ink, -post: List<&2, Tk.Ink>, split: {Tk.pairs() == List.append(&2, Tk.Ink, pre, p <> post) : List<&2, Tk.Ink>}) -> {Tk.readable.all(m, List.append(&2, Tk.Ink, pre, p <> post)) == True{} : Bool}:
  %split : {Tk.readable.all(m, _) == True{} : Bool}
  pt.all_readable(m)

def tokens_legible(m: Tk.Mode, +pre: List<&2, Tk.Ink>, p: Tk.Ink, +post: List<&2, Tk.Ink>, split: {Tk.pairs() == List.append(&2, Tk.Ink, pre, p <> post) : List<&2, Tk.Ink>}) -> {Tk.readable(m, p) == True{} : Bool}:
  +m1 = m
  +p1 = p
  tokens.pt.pick(m1, pre, p1, post, pt.whole(m1, pre, p1, post, split))

def Tokens.tokens_legible(m, pre, p, post, split):
  tokens_legible(m, pre, p, post, split)

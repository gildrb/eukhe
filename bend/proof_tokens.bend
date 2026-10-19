# proof_tokens: the T2 laws (docs/dashboard.md "Tokens") of the token
# model in bend/tokens.bend.
#
# The tables are constants, so each claim about them computes: the
# lookup of every tone in each mode, the readable test of the pair list
# in each mode (bend/color.bend's exact contrast), and the ascent of each
# scale. A pair taken from the list (pairs = pre ++ [p] ++ post) is
# readable because the whole list is: `pt.pick` walks pre.

import Base
import ./tokens.bend as Tk

# Logic
# -----

def pt.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pt.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pt.BD(_, A, Unit)
  Unit{}

def pt.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pt.absurdF({False{} == True{} : Bool}, h)

def pt.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pt.absurdF({b == True{} : Bool}, h)

# The palette
# -----------

def pt.paired_light(t: Tk.Tone) -> {Maybe.is_some(&2, Tk.Col, Tk.find(t, Tk.palette(Tk.Light{}))) == True{} : Bool}:
  match t:
    case Tk.Bg{}:
      {==}
    case Tk.Sidebar{}:
      {==}
    case Tk.Raised{}:
      {==}
    case Tk.Surface{}:
      {==}
    case Tk.Hover{}:
      {==}
    case Tk.Primary{}:
      {==}
    case Tk.Secondary{}:
      {==}
    case Tk.Tertiary{}:
      {==}
    case Tk.Hairline{}:
      {==}
    case Tk.Scrim{}:
      {==}
    case Tk.Danger{}:
      {==}
    case Tk.Selection{}:
      {==}
    case Tk.Scrollbar{}:
      {==}
    case Tk.ShadowNear{}:
      {==}
    case Tk.ShadowFar{}:
      {==}
    case Tk.ShadowDrawer{}:
      {==}
    case Tk.ShadowLatest{}:
      {==}

def pt.paired_dark(t: Tk.Tone) -> {Maybe.is_some(&2, Tk.Col, Tk.find(t, Tk.palette(Tk.Dark{}))) == True{} : Bool}:
  match t:
    case Tk.Bg{}:
      {==}
    case Tk.Sidebar{}:
      {==}
    case Tk.Raised{}:
      {==}
    case Tk.Surface{}:
      {==}
    case Tk.Hover{}:
      {==}
    case Tk.Primary{}:
      {==}
    case Tk.Secondary{}:
      {==}
    case Tk.Tertiary{}:
      {==}
    case Tk.Hairline{}:
      {==}
    case Tk.Scrim{}:
      {==}
    case Tk.Danger{}:
      {==}
    case Tk.Selection{}:
      {==}
    case Tk.Scrollbar{}:
      {==}
    case Tk.ShadowNear{}:
      {==}
    case Tk.ShadowFar{}:
      {==}
    case Tk.ShadowDrawer{}:
      {==}
    case Tk.ShadowLatest{}:
      {==}

def tokens_paired(t: Tk.Tone, m: Tk.Mode) -> {Maybe.is_some(&2, Tk.Col, Tk.find(t, Tk.palette(m))) == True{} : Bool}:
  match m:
    case Tk.Light{}:
      pt.paired_light(t)
    case Tk.Dark{}:
      pt.paired_dark(t)

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
def pt.pick(+m: Tk.Mode, +pre: List<&2, Tk.Ink>, +p: Tk.Ink, +post: List<&2, Tk.Ink>, h: {Tk.readable.all(m, List.append(&2, Tk.Ink, pre, p <> post)) == True{} : Bool}) -> {Tk.readable(m, p) == True{} : Bool}:
  match pre:
    case Nil{}:
      pt.and_l(Tk.readable(m, p), Tk.readable.all(m, post), h)
    case Con{+q, +rest}:
      pt.pick(m, rest, p, post, pt.and_r(Tk.readable(m, q), Tk.readable.all(m, List.append(&2, Tk.Ink, rest, p <> post)), h))

# the split list is the pair list, which is readable
def pt.whole(+m: Tk.Mode, -pre: List<&2, Tk.Ink>, -p: Tk.Ink, -post: List<&2, Tk.Ink>, split: {Tk.pairs() == List.append(&2, Tk.Ink, pre, p <> post) : List<&2, Tk.Ink>}) -> {Tk.readable.all(m, List.append(&2, Tk.Ink, pre, p <> post)) == True{} : Bool}:
  %split : {Tk.readable.all(m, _) == True{} : Bool}
  pt.all_readable(m)

def tokens_legible(m: Tk.Mode, +pre: List<&2, Tk.Ink>, p: Tk.Ink, +post: List<&2, Tk.Ink>, split: {Tk.pairs() == List.append(&2, Tk.Ink, pre, p <> post) : List<&2, Tk.Ink>}) -> {Tk.readable(m, p) == True{} : Bool}:
  +m1 = m
  +p1 = p
  pt.pick(m1, pre, p1, post, pt.whole(m1, pre, p1, post, split))

# The scales
# ----------

def tokens_layers_ordered() -> {Tk.ascends(Tk.layers()) == True{} : Bool}:
  {==}

def tokens_space_ascends() -> {Tk.ascends(Tk.space()) == True{} : Bool}:
  {==}

def tokens_type_ascends() -> {Bool.and(Tk.ascends(Tk.sizes()), Tk.ascends(Tk.lines())) == True{} : Bool}:
  {==}

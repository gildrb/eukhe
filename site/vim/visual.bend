# eukhe.com's Neovim: visual mode
# ===============================
#
# What a visual selection holds and where it shows. The selection runs
# from where it started to the cursor, either way round: characters (v),
# both ends included, or whole lines (V). Yanked, it is the text the
# clipboard gets; on screen, one run of cells per row it covers.

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B
import ./view.bend as V
import ./st.bend as S

# Ends
# ----

# a comes no later than b
def Vis.le(+a: T.Pos, +b: T.Pos) -> Bool:
  +la = S.Pos.line(a)
  +lb = S.Pos.line(b)
  Bool.or(Nat.is_lt(la, lb), Bool.and(Nat.is_eq(la, lb), Nat.is_le(S.Pos.col(a), S.Pos.col(b))))

# the selection's first and last ends
def Vis.lo(+a: T.Pos, +b: T.Pos) -> T.Pos:
  Bool.pick(T.Pos, Vis.le(a, b), a, b)

def Vis.hi(+a: T.Pos, +b: T.Pos) -> T.Pos:
  Bool.pick(T.Pos, Vis.le(a, b), b, a)

# The text
# --------

# a file's text: its lines, each ended by a newline
def Vis.join(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{h, t}:
      String.append(h, String.append("\n", Vis.join(t)))

# the characters of s
def Vis.size(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+Vis.size(t)

# where line l starts in that text
def Vis.off(l: Nat, ls: List<&2, String>) -> Nat:
  match l ls:
    case 0n _:
      0n
    case 1n+p Nil{}:
      0n
    case 1n+p Con{h, t}:
      Nat.add(Vis.size(h), 1n+Vis.off(p, t))

# the first n characters of s
def Vis.take(s: String, n: Nat) -> String:
  match s n:
    case SNil{} _:
      SNil{}
    case SCon{h, t} 0n:
      SNil{}
    case SCon{h, t} 1n+p:
      SCon{h, Vis.take(t, p)}

# where a selection of kind k from p to q (p first) starts and ends in the
# text of lines ls: characters from p's to q's, both included (on an empty
# line, the character is its line break, as in Neovim); lines whole, with
# their line breaks
def Vis.ends(k: T.Vis, +ls: List<&2, String>, +p: T.Pos, +q: T.Pos) -> (Nat & Nat):
  match k:
    case T.VChars{}:
      +l1 = S.Pos.line(p)
      +l2 = S.Pos.line(q)
      (Nat.add(Vis.off(l1, ls), S.Pos.col(p)), Nat.add(Vis.off(l2, ls), 1n+S.Pos.col(q)))
    case T.VLines{}:
      (Vis.off(S.Pos.line(p), ls), Vis.off(1n+S.Pos.line(q), ls))

# the run of text from..to
def Vis.cut(+text: String, ft: (Nat & Nat)) -> String:
  match ft:
    case (+from, to):
      Vis.take(X.Text.drop(text, from), Nat.sub(to, from))

# what a selection of kind k from a to b of lines ls holds (y copies it):
# a run of the text of ls
def Vis.text(+k: T.Vis, +ls: List<&2, String>, +a: T.Pos, +b: T.Pos) -> String:
  Vis.cut(Vis.join(ls), Vis.ends(k, ls, Vis.lo(a, b), Vis.hi(a, b)))

# On screen
# ---------

# the columns from..to (to excluded) of line l, n characters long, that a
# selection of kind k from p to q (p first) covers; an empty line shows
# one cell; a line outside it, none
def Vis.cols(k: T.Vis, +l: Nat, +n: Nat, +p: T.Pos, +q: T.Pos) -> (Nat & Nat):
  match k:
    case T.VChars{}:
      +l1 = S.Pos.line(p)
      +l2 = S.Pos.line(q)
      Bool.pick((Nat & Nat), Bool.and(Nat.is_le(l1, l), Nat.is_le(l, l2)), (Bool.pick(Nat, Nat.is_eq(l, l1), S.Pos.col(p), 0n), Bool.pick(Nat, Nat.is_eq(l, l2), 1n+S.Pos.col(q), Nat.max(n, 1n))), (0n, 0n))
    case T.VLines{}:
      Bool.pick((Nat & Nat), Bool.and(Nat.is_le(S.Pos.line(p), l), Nat.is_le(l, S.Pos.line(q))), (0n, Nat.max(n, 1n)), (0n, 0n))

# columns from..to as a run on screen row r, if any of it shows
def Vis.span(ft: (Nat & Nat), +r: Nat, +left: Nat, +w: Nat, +g: Nat) -> Maybe<&2, T.Span>:
  match ft:
    case (+from, to):
      V.View.span(r, from, Nat.sub(to, from), left, w, g)

def Vis.go(h: Nat, ls: List<&2, String>, +k: T.Vis, +l: Nat, +r: Nat, +p: T.Pos, +q: T.Pos, +left: Nat, +w: Nat, +g: Nat, +acc: List<&2, T.Span>) -> List<&2, T.Span>:
  match h ls:
    case 0n _:
      List.reverse(&2, T.Span, acc)
    case 1n+n Nil{}:
      List.reverse(&2, T.Span, acc)
    case 1n+n Con{line, t}:
      Vis.go(n, t, k, 1n+l, 1n+r, p, q, left, w, g, V.View.span.put(Vis.span(Vis.cols(k, l, X.Text.len(line), p, q), r, left, w, g), acc))

# the selection's runs on the h text rows from line top, columns left
# to left + w - 1, the text starting at screen column g
def Vis.spans(+k: T.Vis, +ls: List<&2, String>, +a: T.Pos, +b: T.Pos, +top: Nat, +h: Nat, +left: Nat, +w: Nat, +g: Nat) -> List<&2, T.Span>:
  Vis.go(h, B.Lines.drop(ls, top), k, top, 0n, Vis.lo(a, b), Vis.hi(a, b), left, w, g, Nil{})

# Modes
# -----

def Vis.label(k: T.Vis) -> String:
  match k:
    case T.VChars{}:
      "-- VISUAL --"
    case T.VLines{}:
      "-- VISUAL LINE --"

def Vis.same(a: T.Vis, b: T.Vis) -> Bool:
  match a b:
    case T.VChars{} T.VChars{}:
      True{}
    case T.VChars{} T.VLines{}:
      False{}
    case T.VLines{} T.VChars{}:
      False{}
    case T.VLines{} T.VLines{}:
      True{}

# a window shows the same buffer as before
def Vis.same_tgt(a: T.Tgt, b: T.Tgt) -> Bool:
  match a b:
    case T.File{i} T.File{j}:
      Nat.is_eq(i, j)
    case T.File{i} T.Dir{q}:
      False{}
    case T.Dir{p} T.File{j}:
      False{}
    case T.Dir{p} T.Dir{q}:
      String.eq(p, q)

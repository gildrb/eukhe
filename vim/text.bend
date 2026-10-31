# eukhe.com's Neovim: text
# ========================
#
# Characters and lines. Every loop over text is a tail call (the JS target
# has a small stack); a line of the docs runs to 2,305 characters.

import Base

# runs found(Unit{}) when hit, else miss(Unit{}): only the taken branch
# runs (the bank's Bool.when)
def Bool.when(-R: Type, hit: Bool, miss: Unit -> R, found: Unit -> R) -> R:
  match hit:
    case True{}:
      found(Unit{})
    case False{}:
      miss(Unit{})

# Characters
# ----------

# Vim's class of a character (utf_class, reduced to the characters these
# files hold): 0 blank, 1 punctuation, 2 a word character ('iskeyword'
# "@,48-57,_,192-255", and letters past 255). Big words (W, B, E) know
# only blank (0) and not (1).
def Char.cls(c: Char, big: Bool) -> Nat:
  match c:
    case Chr{+x}:
      +blank = Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 9), Bool.or(U32.is_eq(x, 160), Bool.and(U32.is_ge(x, 8192), U32.is_le(x, 8203)))))
      +word = Bool.or(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), Bool.or(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90)), Bool.or(Bool.and(U32.is_ge(x, 97), U32.is_le(x, 122)), Bool.or(U32.is_eq(x, 95), Bool.or(Bool.and(Bool.and(U32.is_ge(x, 192), U32.is_le(x, 255)), Bool.and(U32.is_ne(x, 215), U32.is_ne(x, 247))), Bool.and(U32.is_ge(x, 256), Bool.not(Bool.and(U32.is_ge(x, 8192), U32.is_le(x, 11263)))))))))
      Bool.pick(Nat, blank, 0n, Bool.pick(Nat, big, 1n, Bool.pick(Nat, word, 2n, 1n)))

# c in lower case: ASCII and Greek capitals (the letters these files hold)
def Char.fold(c: Char) -> Char:
  match c:
    case Chr{+x}:
      +ascii = Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90))
      +greek = Bool.and(Bool.and(U32.is_ge(x, 913), U32.is_le(x, 937)), U32.is_ne(x, 930))
      Chr{Bool.pick(U32, Bool.or(ascii, greek), U32.add(x, 32), x)}

def Char.upper(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.not(Char.is_eq(Chr{x}, Char.fold(Chr{x})))

# UTF-8 bytes of c (the statusline's %c counts bytes)
def Char.bytes(c: Char) -> Nat:
  match c:
    case Chr{+x}:
      Bool.pick(Nat, U32.is_lt(x, 128), 1n, Bool.pick(Nat, U32.is_lt(x, 2048), 2n, Bool.pick(Nat, U32.is_lt(x, 65536), 3n, 4n)))

# Lines
# -----

def Text.len.go(s: String, acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      Text.len.go(t, 1n+acc)

# the characters in s
def Text.len(s: String) -> Nat:
  Text.len.go(s, 0n)

# the last column a cursor may take on a line of n characters: n - 1, or 0
# on an empty line
def Text.last(n: Nat) -> Nat:
  Nat.sub(n, 1n)

# character i of s
def Text.at(s: String, i: Nat) -> Maybe<&2, Char>:
  match s i:
    case SNil{} _:
      None{}
    case SCon{h, t} 0n:
      Some{h}
    case SCon{h, t} 1n+p:
      Text.at(t, p)

# s from character i on
def Text.drop(s: String, i: Nat) -> String:
  match s i:
    case SNil{} _:
      SNil{}
    case SCon{h, t} 0n:
      SCon{h, t}
    case SCon{h, t} 1n+p:
      Text.drop(t, p)

# s less its first character. Strings built a character at a time (the
# loops below, from a blank) end with it: on the JS target the cut leaves
# one flat string, which the next walk over it and String.contains read
# fastest
def Text.rest(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      t

def Text.take.go(s: String, n: Nat, +acc: String) -> String:
  match s n:
    case SNil{} _:
      Text.rest(acc)
    case SCon{h, t} 0n:
      Text.rest(acc)
    case SCon{h, t} 1n+p:
      Text.take.go(t, p, String.append(acc, SCon{h, SNil{}}))

# the first n characters of s
def Text.take(s: String, n: Nat) -> String:
  Text.take.go(s, n, " ")

def Text.first.go(s: String, +i: Nat, +last: Nat) -> Nat:
  match s:
    case SNil{}:
      last
    case SCon{+h, t}:
      Bool.when(Nat, Nat.is_eq(Char.cls(h, True{}), 0n), u => i, u => Text.first.go(t, 1n+i, last))

# the column of s's first non-blank character; its last column when it is
# all blank (^)
def Text.first(+s: String) -> Nat:
  Text.first.go(s, 0n, Text.last(Text.len(s)))

def Text.bytes.go(s: String, n: Nat, acc: Nat) -> Nat:
  match s n:
    case SNil{} _:
      acc
    case SCon{h, t} 0n:
      acc
    case SCon{h, t} 1n+p:
      Text.bytes.go(t, p, Nat.add(acc, Char.bytes(h)))

# the UTF-8 bytes before column n of s
def Text.bytes(s: String, n: Nat) -> Nat:
  Text.bytes.go(s, n, 0n)

def Text.fold.go(s: String, +acc: String) -> String:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      Text.fold.go(t, String.append(acc, SCon{Char.fold(h), SNil{}}))

# s in lower case
def Text.fold(s: String) -> String:
  Text.rest(Text.fold.go(s, " "))

# whether s holds a capital letter
def Text.has_upper(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      Bool.when(Bool, Char.upper(h), u => Text.has_upper(t), u => True{})

def Text.prefix.go(s: String, p: String, +ok: Bool) -> Bool:
  match s p:
    case _ SNil{}:
      ok
    case SNil{} SCon{y, yt}:
      False{}
    case SCon{+x, xt} SCon{+y, yt}:
      Text.prefix.go(xt, Bool.pick(String, Char.is_eq(x, y), yt, ""), Bool.and(ok, Char.is_eq(x, y)))

# whether s starts with p
def Text.prefix(p: String, s: String) -> Bool:
  Text.prefix.go(s, p, True{})

# the decimal digits of n
def Text.digits(n: Nat) -> Nat:
  Text.len(Nat.show(n))

def Text.spaces(n: Nat, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      Text.spaces(p, SCon{' ', acc})

# s right-aligned in w cells
def Text.right(+s: String, w: Nat) -> String:
  Text.spaces(Nat.sub(w, Text.len(s)), s)

# s left-aligned in w cells
def Text.leftpad(+s: String, w: Nat) -> String:
  String.append(s, Text.spaces(Nat.sub(w, Text.len(s)), SNil{}))

# Cells
# -----
#
# A screen cell holds one character; fff's goose (U+1FABF) takes two.

# the cells character c takes
def Char.width(c: Char) -> Nat:
  match c:
    case Chr{+x}:
      Bool.pick(Nat, U32.is_eq(x, 129727), 2n, 1n)

def Text.cells.go(s: String, acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      Text.cells.go(t, Nat.add(acc, Char.width(h)))

# the cells s takes
def Text.cells(s: String) -> Nat:
  Text.cells.go(s, 0n)

def Text.cells.upto.go(s: String, n: Nat, +acc: Nat) -> Nat:
  match s n:
    case SNil{} _:
      acc
    case SCon{h, t} 0n:
      acc
    case SCon{h, t} 1n+p:
      Text.cells.upto.go(t, p, Nat.add(acc, Char.width(h)))

# the cells of s's first n characters: Text.cells(s) when s holds at most
# n, else at least n
def Text.cells.upto(s: String, n: Nat) -> Nat:
  Text.cells.upto.go(s, n, 0n)

def Text.cut.go(s: String, w: Nat, +acc: String) -> String:
  match s w:
    case SNil{} _:
      Text.rest(acc)
    case SCon{h, t} 0n:
      Text.rest(acc)
    case SCon{+h, t} 1n++p:
      +cw = Char.width(h)
      +ok = Nat.is_le(cw, 1n+p)
      Text.cut.go(t, Bool.pick(Nat, ok, Nat.sub(1n+p, cw), 0n), Bool.pick(String, ok, String.append(acc, SCon{h, SNil{}}), acc))

# s cut to at most w cells
def Text.cut(s: String, w: Nat) -> String:
  Text.cut.go(s, w, " ")

# s's characters while they fit in w cells, then pad more blanks (a
# character that does not fit leaves its cells to pad)
def Text.fit.go(s: String, w: Nat, +pad: Nat, +acc: String) -> String:
  match s w:
    case SNil{} _:
      Text.rest(String.append(acc, Text.spaces(Nat.add(w, pad), SNil{})))
    case SCon{h, t} 0n:
      Text.rest(String.append(acc, Text.spaces(pad, SNil{})))
    case SCon{+h, t} 1n++p:
      +cw = Char.width(h)
      +ok = Nat.is_le(cw, 1n+p)
      Text.fit.go(t, Bool.pick(Nat, ok, Nat.sub(1n+p, cw), 0n), Bool.pick(Nat, ok, pad, 1n+p), Bool.pick(String, ok, String.append(acc, SCon{h, SNil{}}), acc))

# s in exactly w cells: cut, then padded with spaces
def Text.fit(+s: String, +w: Nat) -> String:
  Text.fit.go(s, w, 0n, " ")

def Text.reps(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      Text.reps(p, c, SCon{c, acc})

# character c n times
def Text.rep(c: Char, n: Nat) -> String:
  Text.reps(n, c, SNil{})

# the blanks at the start of s dropped
def Text.trim_start(s: String) -> String:
  match s:
    case SCon{' ', t}:
      Text.trim_start(t)
    case SCon{'\t', t}:
      Text.trim_start(t)
    case t:
      t

# the blanks s starts with
def Text.indent(s: String, acc: Nat) -> Nat:
  match s:
    case SCon{' ', t}:
      Text.indent(t, 1n+acc)
    case SCon{'\t', t}:
      Text.indent(t, 1n+acc)
    case t:
      acc

def Text.dropc.go(s: String, n: Nat, +pre: String) -> String:
  match s n:
    case t 0n:
      String.append(pre, t)
    case SNil{} 1n+p:
      SNil{}
    case SCon{h, t} 1n++p:
      +wide = Nat.is_eq(Char.width(h), 2n)
      +half = Bool.and(wide, Nat.is_eq(p, 0n))
      Text.dropc.go(t, Bool.pick(Nat, half, 0n, Nat.sub(p, Bool.pick(Nat, wide, 1n, 0n))), Bool.pick(String, half, " ", ""))

# s less its first n cells (a wide character cut in two leaves a space)
def Text.dropc(s: String, n: Nat) -> String:
  Text.dropc.go(s, n, "")

# s with text over it from cell col on (virtual text at a window column),
# as wide as base (what runs past its edge is cut)
def Text.over(+base: String, +col: Nat, +s: String) -> String:
  +w = Text.cells(s)
  Text.fit(Text.fit(Text.cut(base, col), col) ++ s ++ Text.dropc(base, Nat.add(col, w)), Text.cells(base))

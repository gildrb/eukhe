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

def Text.take.go(s: String, n: Nat, acc: String) -> String:
  match s n:
    case SNil{} _:
      String.reverse(acc)
    case SCon{h, t} 0n:
      String.reverse(acc)
    case SCon{h, t} 1n+p:
      Text.take.go(t, p, SCon{h, acc})

# the first n characters of s
def Text.take(s: String, n: Nat) -> String:
  Text.take.go(s, n, SNil{})

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

def Text.fold.go(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{h, t}:
      Text.fold.go(t, SCon{Char.fold(h), acc})

# s in lower case
def Text.fold(s: String) -> String:
  Text.fold.go(s, SNil{})

# whether s holds a capital letter
def Text.has_upper(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      Bool.when(Bool, Char.upper(h), u => Text.has_upper(t), u => True{})

# whether s starts with p
def Text.prefix(p: String, s: String) -> Bool:
  match p s:
    case SNil{} _:
      True{}
    case SCon{y, yt} SNil{}:
      False{}
    case SCon{+y, yt} SCon{+x, xt}:
      Bool.when(Bool, Char.is_eq(x, y), u => False{}, u => Text.prefix(yt, xt))

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

def Text.cut.go(s: String, +w: Nat, +acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{+h, t}:
      +cw = Char.width(h)
      Bool.when(String, Nat.is_le(cw, w), u => String.reverse(acc), u => Text.cut.go(t, Nat.sub(w, cw), SCon{h, acc}))

# s cut to at most w cells
def Text.cut(s: String, w: Nat) -> String:
  Text.cut.go(s, w, SNil{})

# s in exactly w cells: cut, then padded with spaces
def Text.fit(+s: String, +w: Nat) -> String:
  +c = Text.cut(s, w)
  String.append(c, Text.spaces(Nat.sub(w, Text.cells(c)), SNil{}))

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

# s less its first n cells (a wide character cut in two leaves a space)
def Text.dropc(s: String, n: Nat) -> String:
  match s n:
    case t 0n:
      t
    case SNil{} 1n+p:
      SNil{}
    case SCon{h, +t} 1n++p:
      +wide = Nat.is_eq(Char.width(h), 2n)
      Bool.when(String, Bool.and(wide, Nat.is_eq(p, 0n)), u => Text.dropc(t, Nat.sub(p, Bool.pick(Nat, wide, 1n, 0n))), u => SCon{' ', t})

# s with text over it from cell col on (virtual text at a window column)
def Text.over(+base: String, +col: Nat, +s: String) -> String:
  +w = Text.cells(s)
  Text.fit(Text.cut(base, col), col) ++ s ++ Text.dropc(base, Nat.add(col, w))

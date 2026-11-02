# autolink_shapes: the shapes of marked 18.0.7's GFM inline autolink rules
# the markdown renderer reads (eukhe-tui autolink.rs; the matcher:
# bend/shape.bend; ids 120-129 of the entry bend/ffi_shape.bend: `shape(i)`
# is the shape of id 120 + i). Above each shape: the regex it
# replaces, verbatim from autolink.rs. `\s` is Unicode White_Space. Where a
# regex repetition can split one run of chars into rounds in many ways,
# the shape reads the run in the one way the regex's first reading takes
# (said at the shape), so that the matcher, which lists every reading of
# a repetition, stays linear in the run. Pure: no IO, no @unsafe.

import Base
import ./shape.bend as S

# Classes
# -------

def rg(+x: U32) -> S.Rg:
  S.Rg{x, x}

# Unicode White_Space (regex `\s`)
def ws_rgs() -> List<&2, S.Rg>:
  [S.Rg{9, 13}, rg(32), rg(133), rg(160), rg(5760), S.Rg{8192, 8202}, S.Rg{8232, 8233}, rg(8239), rg(8287), rg(12288)]

def cls(rs: List<&2, S.Rg>) -> S.Cls:
  S.Cls{S.Codes{rs}, False{}, False{}}

def but(rs: List<&2, S.Rg>) -> S.Cls:
  S.Cls{S.Codes{rs}, True{}, False{}}

def one(c: S.Cls) -> S.Piece:
  S.Run{c, 1n, Some{1n}}

def plus(c: S.Cls) -> S.Piece:
  S.Run{c, 1n, None{}}

def star(c: S.Cls) -> S.Piece:
  S.Run{c, 0n, None{}}

# `[a-zA-Z0-9]`
def alnum() -> S.Cls:
  cls([S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}])

# `[a-zA-Z0-9-]`
def label() -> S.Cls:
  cls([rg(45), S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}])

# `[a-zA-Z0-9-_]`
def label_() -> S.Cls:
  cls([rg(45), S.Rg{48, 57}, S.Rg{65, 90}, rg(95), S.Rg{97, 122}])

# `(?![-_])`
def no_dash() -> S.Piece:
  S.Ahead{[one(cls([rg(45), rg(95)]))], True{}}

# `(?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?`
def label_tail() -> S.Piece:
  S.Opt{[S.Run{label(), 0n, Some{61n}}, one(alnum())]}

# The shapes
# ----------

# 120 `^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>`
def angle() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"<"}, S.Cap{[S.Alt{[one(cls([S.Rg{65, 90}, S.Rg{97, 122}])), S.Run{cls([rg(43), S.Rg{45, 46}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]), 1n, Some{31n}}, S.Lit{":"}, star(but(List.append(&2, S.Rg, ws_rgs(), [S.Rg{0, 32}, rg(60), rg(62)])))], [plus(cls([rg(33), S.Rg{35, 39}, S.Rg{42, 43}, S.Rg{45, 57}, rg(61), rg(63), S.Rg{65, 90}, S.Rg{94, 126}])), S.Cap{[S.Lit{"@"}]}, one(alnum()), label_tail(), S.Many{[S.Lit{"."}, one(alnum()), label_tail()], 1n}, no_dash()]}]}, S.Lit{">"}], False{}}

# 121 `^((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP])://|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|^[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![-_])`:
# after the scheme, the repetition `(?:[a-zA-Z0-9\-]+\.?)+` reads its
# chars first, then `[^\s<]*` the rest, and every char the repetition
# can read is one `[^\s<]` takes too: so the url is the scheme, a letter,
# digit or `-`, then every char up to the first White_Space or `<`
def bare() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Alt{[S.Cap{[S.Alt{[S.Alt{[S.Fold{"http"}, S.Opt{[S.Fold{"s"}]}], [S.Fold{"ftp"}]}, S.Lit{"://"}], [S.Lit{"www."}]}]}, one(label()), star(but(List.append(&2, S.Rg, ws_rgs(), [rg(60)])))], [plus(cls([rg(43), S.Rg{45, 46}, S.Rg{48, 57}, S.Rg{65, 90}, rg(95), S.Rg{97, 122}])), S.Cap{[S.Lit{"@"}]}, plus(label_()), S.Many{[S.Lit{"."}, star(label_()), one(alnum())], 1n}, no_dash()]}], False{}}

# the chars of a trailing punctuation run: `[?!.,:;*_'"~)]`
def punct() -> S.Cls:
  cls([rg(33), rg(34), rg(39), rg(41), rg(42), rg(44), rg(46), rg(58), rg(59), rg(63), rg(95), rg(126)])

# 122 `(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+`:
# each round reads, by its first char (the options start on different
# chars, so at most one fits): a whole run of chars none of
# `?!.,:;*_'"~()&`; or `(`, chars that are no `)`, `)`; or `&` not before
# letters and digits, `;` and the end; or a whole run of punctuation that
# does not reach the end, else all of such a run but its last char (the
# regex's first reading takes each run whole, or, before `(?!$)`, all
# but one char, and never goes back on a round, since nothing follows)
def backpedal() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Many{[S.Alt{[plus(but([rg(33), rg(34), rg(38), rg(39), rg(40), rg(41), rg(42), rg(44), rg(46), rg(58), rg(59), rg(63), rg(95), rg(126)])), S.Ahead{[one(but([rg(33), rg(34), rg(38), rg(39), rg(40), rg(41), rg(42), rg(44), rg(46), rg(58), rg(59), rg(63), rg(95), rg(126)]))], True{}}], [S.Alt{[S.Lit{"("}, star(but([rg(41)])), S.Lit{")"}], [S.Alt{[S.Lit{"&"}, S.Ahead{[plus(alnum()), S.Lit{";"}, S.End{}], True{}}], [S.Alt{[plus(punct()), S.Ahead{[one(punct())], True{}}, S.Ahead{[S.End{}], True{}}], [plus(punct()), S.Ahead{[one(punct()), S.End{}], False{}}]}]}]}]}], 1n}], False{}}

# The table: the shape of id 120 + i at index i (none past the last); a
# lookup builds only the shape it answers
def shape(i: Nat) -> Maybe<&2, S.Shape>:
  match i:
    case 0n:
      Some{angle()}
    case 1n:
      Some{bare()}
    case 2n:
      Some{backpedal()}
    case 3n+k:
      None{}

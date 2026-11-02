# arg_token_shapes: the shapes of the `@path` and `--flag` argument tokens
# the prompt highlighter colors (eukhe-tui prompt_highlight.rs, TS
# prompt-highlight.ts ARG_TOKEN_PATTERN; the matcher: bend/shape.bend;
# ids 110-119 of the entry bend/ffi_shape.bend: `shape(i)` is the shape of
# id 110 + i). Above each shape: the regex it replaces. `\s`
# is Unicode White_Space. Pure: no IO, no @unsafe.

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

# `[^\s\x1b]`
def free() -> S.Cls:
  but(List.append(&2, S.Rg, ws_rgs(), [rg(27)]))

# `\\[^\s\x1b]`: a backslash and the char it escapes
def escaped() -> List<&2, S.Piece>:
  [one(cls([rg(92)])), one(free())]

# `@"[^"\n]*"`
def quoted() -> List<&2, S.Piece>:
  [S.Lit{"@\""}, S.Run{but([rg(10), rg(34)]), 0n, None{}}, S.Lit{"\""}]

# `@(?:\\[^\s\x1b]|[^\s\x1b|])+`: each round reads an escape when one is
# there, else one char that is no White_Space, no ESC and no `|` (the
# regex takes the escape first; no reading of it ever goes back on that
# choice, since nothing follows the repetition, so one reading per round
# fits the same text)
def path() -> List<&2, S.Piece>:
  [S.Lit{"@"}, S.Many{[S.Alt{escaped(), [S.Ahead{escaped(), True{}}, one(but(List.append(&2, S.Rg, ws_rgs(), [rg(27), rg(124)])))]}], 1n}]

# `--[A-Za-z0-9][A-Za-z0-9-]*`
def flag() -> List<&2, S.Piece>:
  [S.Lit{"--"}, one(cls([S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}])), S.Run{cls([rg(45), S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]), 0n, None{}}]

# `--(?=\s|$)`
def separator() -> List<&2, S.Piece>:
  [S.Lit{"--"}, S.Ahead{[S.Alt{[one(S.Cls{S.Space{}, False{}, False{}})], [S.End{}]}], False{}}]

# The shapes
# ----------

# 110 `@"[^"\n]*"|@(?:\\[^\s\x1b]|[^\s\x1b|])+|--[A-Za-z0-9][A-Za-z0-9-]*`
def plain() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Alt{quoted(), [S.Alt{path(), flag()}]}], False{}}

# 111 `@"[^"\n]*"|@(?:\\[^\s\x1b]|[^\s\x1b|])+|--[A-Za-z0-9][A-Za-z0-9-]*|--(?=\s|$)`
def with_separator() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Alt{quoted(), [S.Alt{path(), [S.Alt{flag(), separator()}]}]}], False{}}

# The table: the shape of id 110 + i at index i (none past the last); a
# lookup builds only the shape it answers
def shape(i: Nat) -> Maybe<&2, S.Shape>:
  match i:
    case 0n:
      Some{plain()}
    case 1n:
      Some{with_separator()}
    case 2n+k:
      None{}

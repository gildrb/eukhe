# eukhe: the laws of area arg_token_shapes

import Base
import ../bend/shape.bend as S
import ../bend/arg_token_shapes.bend as AT

# (AT1) The shapes of the prompt's argument tokens
# ------------------------------------------------
# bend/arg_token_shapes.bend, ids 110-119 of the entry bend/ffi_shape.bend
# (eukhe-tui prompt_highlight.rs asks them through eukhe-tui
# text_shapes.rs, in place of TS ARG_TOKEN_PATTERN and
# ARG_TOKEN_PATTERN_WITH_SEPARATOR). The matcher is pinned by
# laws/shape/match.bend and laws/shape/search.bend. "White_Space" is
# Unicode White_Space (9-13, space, U+0085, U+00A0, U+1680, U+2000-U+200A,
# U+2028, U+2029, U+202F, U+205F, U+3000); "ESC" is U+001B; "an ASCII
# letter or digit" A-Z, a-z, 0-9. "the text holds one of" reads the
# options in order at the leftmost place one fits. A class lists its
# White_Space ranges first, then its other codes, each from the lowest up.
#
# R1: id 110, an argument token: the text holds one of `@"`, chars none of
#     line feed and `"` (none too), `"`; `@`, then one or more rounds, each
#     a backslash and one char that is no White_Space and no ESC when those
#     two come next, else one char that is no White_Space, no ESC and no
#     `|` (the regex takes the escape first and nothing after the rounds
#     makes it go back on a round); `--`, an ASCII letter or digit, then
#     ASCII letters, digits and `-` (none too).
# R2: id 111, an argument token or separator: the text holds one of the
#     three options of R1 in their order, or `--` where one White_Space
#     char or the text end comes next.
# R3: the table holds exactly these shapes, the one of id 110 + i at index
#     i, and no other.
#
# Anchored only: R1 and R2 (arg_token_shapes_example). No source
# outside eukhe's code states the shapes (no requirement holds a token regex;
# the TS regexes are written above each shape of bend/arg_token_shapes.bend
# and above), so a law over the table would compare it with itself; a law
# by meaning over every text needs the matcher's search (bend/shape.bend)
# reasoned through for these shapes, not done. R3 (ids, none past the
# last) is stated for the entry by laws/shape/entry.bend (area shape),
# which reads sp_table.

# Spec helpers
# ------------

def sp_r(+x: U32) -> S.Rg:
  S.Rg{x, x}

def sp_white() -> List<&2, S.Rg>:
  [S.Rg{9, 13}, sp_r(32), sp_r(133), sp_r(160), sp_r(5760), S.Rg{8192, 8202}, S.Rg{8232, 8233}, sp_r(8239), sp_r(8287), sp_r(12288)]

def sp_in(rs: List<&2, S.Rg>) -> S.Cls:
  S.Cls{S.Codes{rs}, False{}, False{}}

def sp_not(rs: List<&2, S.Rg>) -> S.Cls:
  S.Cls{S.Codes{rs}, True{}, False{}}

def sp_1(c: S.Cls) -> S.Piece:
  S.Run{c, 1n, Some{1n}}

# a backslash and one char that is no White_Space and no ESC
def sp_escape() -> List<&2, S.Piece>:
  [sp_1(sp_in([sp_r(92)])), sp_1(sp_not(List.append(&2, S.Rg, sp_white(), [sp_r(27)])))]

# R1: the three options
def sp_quoted() -> List<&2, S.Piece>:
  [S.Lit{"@\""}, S.Run{sp_not([sp_r(10), sp_r(34)]), 0n, None{}}, S.Lit{"\""}]

def sp_path() -> List<&2, S.Piece>:
  [S.Lit{"@"}, S.Many{[S.Alt{sp_escape(), [S.Ahead{sp_escape(), True{}}, sp_1(sp_not(List.append(&2, S.Rg, sp_white(), [sp_r(27), sp_r(124)])))]}], 1n}]

def sp_flag() -> List<&2, S.Piece>:
  [S.Lit{"--"}, sp_1(sp_in([S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}])), S.Run{sp_in([sp_r(45), S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]), 0n, None{}}]

# R2: the separator
def sp_separator() -> List<&2, S.Piece>:
  [S.Lit{"--"}, S.Ahead{[S.Alt{[sp_1(S.Cls{S.Space{}, False{}, False{}})], [S.End{}]}], False{}}]

# R1, R2, by id from 110: the shapes written out, read by
# laws/shape/entry.bend (sp_shape_of, area shape) for ids 110-119; no law
# of this area uses it
def sp_table() -> List<&2, S.Shape>:
  [S.Shape{S.Anywhere{}, [S.Alt{sp_quoted(), [S.Alt{sp_path(), sp_flag()}]}], False{}},
   S.Shape{S.Anywhere{}, [S.Alt{sp_quoted(), [S.Alt{sp_path(), [S.Alt{sp_flag(), sp_separator()}]}]}], False{}}]

# Laws
# ----

# LAW arg_token_shapes_example (R1, R2): anchor: the highlighter tests'
# texts (crates/eukhe-tui/src/prompt_highlight.rs tests): a path and a
# flag; a bare `--` only with the separator shape; a quoted path, an
# unclosed one (read as a plain path) and an escaped one; a path after a
# space; a path then a flag
# EXCLUDES: a token shape that drifts from the highlighter tests (an
#   option lost or reordered, a quote or escape misread, the separator
#   without its lookahead)
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   no source outside eukhe states the shapes (see R1 and R2 above)
law arg_token_shapes_example:
  {[S.all(AT.plain(), "fix @Cargo.toml --quiet now"), S.all(AT.plain(), "x -- y"), S.all(AT.with_separator(), "x -- y"), S.all(AT.plain(), "a @\"my file\" b"), S.all(AT.plain(), "a @\"open b"), S.all(AT.plain(), "a @pa\\th b"), S.all(AT.plain(), "a @b"), S.all(AT.plain(), "@a --b")] == [[S.Fit{4n, 15n, []}, S.Fit{16n, 23n, []}], [], [S.Fit{2n, 4n, []}], [S.Fit{2n, 12n, []}], [S.Fit{2n, 8n, []}], [S.Fit{2n, 8n, []}], [S.Fit{2n, 4n, []}], [S.Fit{0n, 2n, []}, S.Fit{3n, 6n, []}]] : List<&2, List<&2, S.Fit>>}

# autolink_shapes: the shapes of marked 18.0.7's GFM inline autolink rules
# the markdown renderer reads (eukhe-tui autolink.rs; the matcher:
# bend/shape.bend; ids 120-129 of the entry bend/ffi_shape.bend: `shape(i)`
# is the shape of id 120 + i). Above each shape: the regex it
# replaces, verbatim from autolink.rs. `\s` is Unicode White_Space. Where a
# regex repetition can split one run of chars into rounds in many ways,
# the shape reads the run in the one way the regex's first reading takes
# (said at the shape), so that its readings stay linear in the run. Each
# shape is written out whole, so the compiled core holds it as a
# constant. Pure: no IO, no @unsafe.

import Base
import ./shape.bend as S

# 120 `^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>`
def angle() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"<"}, S.Cap{[S.Alt{[S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{43, 43}, S.Rg{45, 46}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{31n}}, S.Lit{":"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{133, 133}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{0, 32}, S.Rg{60, 60}, S.Rg{62, 62}]}, True{}, False{}}, 0n, None{}}], [S.Run{S.Cls{S.Codes{[S.Rg{33, 33}, S.Rg{35, 39}, S.Rg{42, 43}, S.Rg{45, 57}, S.Rg{61, 61}, S.Rg{63, 63}, S.Rg{65, 90}, S.Rg{94, 126}]}, False{}, False{}}, 1n, None{}}, S.Cap{[S.Lit{"@"}]}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{45, 45}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 0n, Some{61n}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Many{[S.Lit{"."}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{45, 45}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 0n, Some{61n}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}]}], 1n}, S.Ahead{[S.Run{S.Cls{S.Codes{[S.Rg{45, 45}, S.Rg{95, 95}]}, False{}, False{}}, 1n, Some{1n}}], True{}}]}]}, S.Lit{">"}], False{}}

# 121 `^((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP])://|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|^[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![-_])`:
# after the scheme, the repetition `(?:[a-zA-Z0-9\-]+\.?)+` reads its
# chars first, then `[^\s<]*` the rest, and every char the repetition
# can read is one `[^\s<]` takes too: so the url is the scheme, a letter,
# digit or `-`, then every char up to the first White_Space or `<`
def bare() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Alt{[S.Cap{[S.Alt{[S.Alt{[S.Fold{"http"}, S.Opt{[S.Fold{"s"}]}], [S.Fold{"ftp"}]}, S.Lit{"://"}], [S.Lit{"www."}]}]}, S.Run{S.Cls{S.Codes{[S.Rg{45, 45}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{133, 133}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{60, 60}]}, True{}, False{}}, 0n, None{}}], [S.Run{S.Cls{S.Codes{[S.Rg{43, 43}, S.Rg{45, 46}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, None{}}, S.Cap{[S.Lit{"@"}]}, S.Run{S.Cls{S.Codes{[S.Rg{45, 45}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, None{}}, S.Many{[S.Lit{"."}, S.Run{S.Cls{S.Codes{[S.Rg{45, 45}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}], 1n}, S.Ahead{[S.Run{S.Cls{S.Codes{[S.Rg{45, 45}, S.Rg{95, 95}]}, False{}, False{}}, 1n, Some{1n}}], True{}}]}], False{}}

# 122 `(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+`:
# each round reads, by its first char (the options start on different
# chars, so at most one fits): a whole run of chars none of
# `?!.,:;*_'"~()&`; or `(`, chars that are no `)`, `)`; or `&` not before
# letters and digits, `;` and the end; or a whole run of punctuation that
# does not reach the end, else all of such a run but its last char (the
# regex's first reading takes each run whole, or, before `(?!$)`, all
# but one char, and never goes back on a round, since nothing follows)
def backpedal() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Many{[S.Alt{[S.Run{S.Cls{S.Codes{[S.Rg{33, 33}, S.Rg{34, 34}, S.Rg{38, 38}, S.Rg{39, 39}, S.Rg{40, 40}, S.Rg{41, 41}, S.Rg{42, 42}, S.Rg{44, 44}, S.Rg{46, 46}, S.Rg{58, 58}, S.Rg{59, 59}, S.Rg{63, 63}, S.Rg{95, 95}, S.Rg{126, 126}]}, True{}, False{}}, 1n, None{}}, S.Ahead{[S.Run{S.Cls{S.Codes{[S.Rg{33, 33}, S.Rg{34, 34}, S.Rg{38, 38}, S.Rg{39, 39}, S.Rg{40, 40}, S.Rg{41, 41}, S.Rg{42, 42}, S.Rg{44, 44}, S.Rg{46, 46}, S.Rg{58, 58}, S.Rg{59, 59}, S.Rg{63, 63}, S.Rg{95, 95}, S.Rg{126, 126}]}, True{}, False{}}, 1n, Some{1n}}], True{}}], [S.Alt{[S.Lit{"("}, S.Run{S.Cls{S.Codes{[S.Rg{41, 41}]}, True{}, False{}}, 0n, None{}}, S.Lit{")"}], [S.Alt{[S.Lit{"&"}, S.Ahead{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 1n, None{}}, S.Lit{";"}, S.End{}], True{}}], [S.Alt{[S.Run{S.Cls{S.Codes{[S.Rg{33, 33}, S.Rg{34, 34}, S.Rg{39, 39}, S.Rg{41, 41}, S.Rg{42, 42}, S.Rg{44, 44}, S.Rg{46, 46}, S.Rg{58, 58}, S.Rg{59, 59}, S.Rg{63, 63}, S.Rg{95, 95}, S.Rg{126, 126}]}, False{}, False{}}, 1n, None{}}, S.Ahead{[S.Run{S.Cls{S.Codes{[S.Rg{33, 33}, S.Rg{34, 34}, S.Rg{39, 39}, S.Rg{41, 41}, S.Rg{42, 42}, S.Rg{44, 44}, S.Rg{46, 46}, S.Rg{58, 58}, S.Rg{59, 59}, S.Rg{63, 63}, S.Rg{95, 95}, S.Rg{126, 126}]}, False{}, False{}}, 1n, Some{1n}}], True{}}, S.Ahead{[S.End{}], True{}}], [S.Run{S.Cls{S.Codes{[S.Rg{33, 33}, S.Rg{34, 34}, S.Rg{39, 39}, S.Rg{41, 41}, S.Rg{42, 42}, S.Rg{44, 44}, S.Rg{46, 46}, S.Rg{58, 58}, S.Rg{59, 59}, S.Rg{63, 63}, S.Rg{95, 95}, S.Rg{126, 126}]}, False{}, False{}}, 1n, None{}}, S.Ahead{[S.Run{S.Cls{S.Codes{[S.Rg{33, 33}, S.Rg{34, 34}, S.Rg{39, 39}, S.Rg{41, 41}, S.Rg{42, 42}, S.Rg{44, 44}, S.Rg{46, 46}, S.Rg{58, 58}, S.Rg{59, 59}, S.Rg{63, 63}, S.Rg{95, 95}, S.Rg{126, 126}]}, False{}, False{}}, 1n, Some{1n}}, S.End{}], False{}}]}]}]}]}], 1n}], False{}}

# The table: the shape of id 120 + i at index i (none past the last)
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


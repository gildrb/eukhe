# arg_token_shapes: the shapes of the `@path` and `--flag` argument tokens
# the prompt highlighter colors (eukhe-tui prompt_highlight.rs, TS
# prompt-highlight.ts ARG_TOKEN_PATTERN; the matcher: bend/shape.bend;
# ids 110-119 of the entry bend/ffi_shape.bend: `shape(i)` is the shape of
# id 110 + i). Above each shape: the regex it replaces. `\s`
# is Unicode White_Space. Each shape is written out whole, so the compiled
# core holds it as a constant. Pure: no IO, no @unsafe.

import Base
import ./shape.bend as S

# 110 `@"[^"\n]*"|@(?:\\[^\s\x1b]|[^\s\x1b|])+|--[A-Za-z0-9][A-Za-z0-9-]*`
def plain() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Alt{[S.Lit{"@\""}, S.Run{S.Cls{S.Codes{[S.Rg{10, 10}, S.Rg{34, 34}]}, True{}, False{}}, 0n, None{}}, S.Lit{"\""}], [S.Alt{[S.Lit{"@"}, S.Many{[S.Alt{[S.Run{S.Cls{S.Codes{[S.Rg{92, 92}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{133, 133}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{27, 27}]}, True{}, False{}}, 1n, Some{1n}}], [S.Ahead{[S.Run{S.Cls{S.Codes{[S.Rg{92, 92}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{133, 133}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{27, 27}]}, True{}, False{}}, 1n, Some{1n}}], True{}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{133, 133}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{27, 27}, S.Rg{124, 124}]}, True{}, False{}}, 1n, Some{1n}}]}], 1n}], [S.Lit{"--"}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{45, 45}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}]}]}], False{}}

# 111 `@"[^"\n]*"|@(?:\\[^\s\x1b]|[^\s\x1b|])+|--[A-Za-z0-9][A-Za-z0-9-]*|--(?=\s|$)`
def with_separator() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Alt{[S.Lit{"@\""}, S.Run{S.Cls{S.Codes{[S.Rg{10, 10}, S.Rg{34, 34}]}, True{}, False{}}, 0n, None{}}, S.Lit{"\""}], [S.Alt{[S.Lit{"@"}, S.Many{[S.Alt{[S.Run{S.Cls{S.Codes{[S.Rg{92, 92}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{133, 133}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{27, 27}]}, True{}, False{}}, 1n, Some{1n}}], [S.Ahead{[S.Run{S.Cls{S.Codes{[S.Rg{92, 92}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{133, 133}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{27, 27}]}, True{}, False{}}, 1n, Some{1n}}], True{}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{133, 133}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{27, 27}, S.Rg{124, 124}]}, True{}, False{}}, 1n, Some{1n}}]}], 1n}], [S.Alt{[S.Lit{"--"}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{45, 45}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}], [S.Lit{"--"}, S.Ahead{[S.Alt{[S.Run{S.Cls{S.Space{}, False{}, False{}}, 1n, Some{1n}}], [S.End{}]}], False{}}]}]}]}], False{}}

# The table: the shape of id 110 + i at index i (none past the last)
def shape(i: Nat) -> Maybe<&2, S.Shape>:
  match i:
    case 0n:
      Some{plain()}
    case 1n:
      Some{with_separator()}
    case 2n+k:
      None{}


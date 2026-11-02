# preview_shapes: the shapes the tool-call code preview reads (eukhe-tui
# code_preview/bash.rs, python.rs and cell.rs, a port of TS
# code-preview.ts and ipython-cell-code.ts; the matcher: bend/shape.bend;
# ids 130-199 of the entry bend/ffi_shape.bend: `shape(i)` is the shape of
# id 130 + i). Above each shape: the regex it replaces, as the
# Rust source spelled it; `{S}` is bash.rs's `S` class
# `[\t\n\x0B\f\r \u{00A0}\u{1680}\u{2000}-\u{200A}\u{2028}\u{2029}\u{202F}\u{205F}\u{3000}\u{FEFF}]`
# (JS `\s`), `{W}` its `W` class `[A-Za-z0-9_]` (JS `\w`). A bare `\s` /
# `\S` is Unicode White_Space or not; `.` any char but a line feed. `\b`
# is an ASCII word boundary here and `\w` an ASCII word char (Rust's are
# Unicode, JS's ASCII: an intended difference); `(?i)` folds ASCII
# letters only (Rust's also takes the Kelvin sign and the long s: an
# intended difference). Each shape is written out whole, so the compiled
# core holds it as a constant. Pure: no IO, no @unsafe.

import Base
import ./shape.bend as S

# 130 `{S}+`
def ws_run() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}], False{}}

# 131 `[A-Za-z0-9+/]{80,}={0,2}`
def blob() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Run{S.Cls{S.Codes{[S.Rg{43, 43}, S.Rg{47, 47}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 80n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{61, 61}]}, False{}, False{}}, 0n, Some{2n}}], False{}}

# 132 `\b((?={W}*(?:token|key|secret|password))[A-Za-z_]{W}*){S}*={S}*(["'])[^"']*\2`
def secret_quoted() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Bound{}, S.Cap{[S.Ahead{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}, S.Alt{[S.Lit{"token"}], [S.Alt{[S.Lit{"key"}], [S.Alt{[S.Lit{"secret"}], [S.Lit{"password"}]}]}]}], False{}}, S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"="}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, True{}, False{}}, 0n, None{}}, S.Same{2n}], False{}}

# 133 `(?i)\b((?={W}*(?:token|key|secret|password))[A-Za-z_]{W}*){S}*={S}*(?!<redacted>)(?!["'])\S+`
def secret_bare() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Bound{}, S.Cap{[S.Ahead{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}, S.Alt{[S.Fold{"token"}], [S.Alt{[S.Fold{"key"}], [S.Alt{[S.Fold{"secret"}], [S.Fold{"password"}]}]}]}], False{}}, S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"="}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Ahead{[S.Fold{"<redacted>"}], True{}}, S.Ahead{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}], True{}}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}], False{}}

# 134 `(?i)\b(authorization:\s*(?:bearer\s+)?)[^\s"']+`
def authorization() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Bound{}, S.Cap{[S.Fold{"authorization:"}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Fold{"bearer"}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 1n, None{}}]}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{133, 133}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{34, 34}, S.Rg{39, 39}]}, True{}, False{}}, 1n, None{}}], False{}}

# 135 `(["'])sk-[^"']+\1`
def sk_key() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Lit{"sk-"}, S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, True{}, False{}}, 1n, None{}}, S.Same{1n}], False{}}

# 136 `(["']).{160,}\1`
def long_string() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 160n, None{}}, S.Same{1n}], False{}}

# 137 `^{S}*!`
def magic() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"!"}], False{}}

# 138 `^{S}*cd{S}+([^&;|]+)(?:&&|;){S}*`
def cd_prefix() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"cd"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{38, 38}, S.Rg{59, 59}, S.Rg{124, 124}]}, True{}, False{}}, 1n, None{}}]}, S.Alt{[S.Lit{"&&"}], [S.Lit{";"}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}], False{}}

# 139 `^{S}*#`
def comment() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"#"}], False{}}

# 140 `^{S}*set{S}+[-+][A-Za-z]*(?:{S}+[-+]?{W}+)*(?:{S}+pipefail)?{S}*$`
def set_line() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"set"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{43, 43}, S.Rg{45, 45}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}, S.Many{[S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{43, 43}, S.Rg{45, 45}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, None{}}], 0n}, S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Lit{"pipefail"}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}], True{}}

# 141 `^(?:export{S}+{W}+=|source{S}+\S+|\.{S}+\S+)`
def env_line() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Alt{[S.Lit{"export"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, None{}}, S.Lit{"="}], [S.Alt{[S.Lit{"source"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}], [S.Lit{"."}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}]}], False{}}

# 142 `"([^"]*)"|'([^']*)'|(\S+)`
def shell_word() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Alt{[S.Lit{"\""}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}]}, True{}, False{}}, 0n, None{}}]}, S.Lit{"\""}], [S.Alt{[S.Lit{"'"}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{39, 39}]}, True{}, False{}}, 0n, None{}}]}, S.Lit{"'"}], [S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}]}]}], False{}}

# 143 `^\./`
def dot_slash() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"./"}], False{}}

# 144 `(?:^|/)vitest/dist/cli\.js$`
def vitest_cli() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Alt{[S.Begin{}], [S.Lit{"/"}]}, S.Lit{"vitest/dist/cli.js"}], True{}}

# 145 `\S*node_modules/\.bin/`
def bin_prefix() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Run{S.Cls{S.Space{}, True{}, False{}}, 0n, None{}}, S.Lit{"node_modules/.bin/"}], False{}}

# 146 `\s*(?:&&|;)\s*`
def chain_sep() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}, S.Alt{[S.Lit{"&&"}], [S.Lit{";"}]}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}], False{}}

# 147 `<<-?\s*['"]?([A-Za-z_][A-Za-z0-9_]*)['"]?`
def heredoc() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Lit{"<<"}, S.Opt{[S.Lit{"-"}]}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}]}, S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}]}], False{}}

# 148 `\b(?:uv{S}+run{S}+)?python3?\b`
def python_run() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Bound{}, S.Opt{[S.Lit{"uv"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Lit{"run"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}]}, S.Lit{"python"}, S.Opt{[S.Lit{"3"}]}, S.Bound{}], False{}}

# 149 `(?<![\w.])(?:bash|sh)\b`: the text start or a char that is no word
# char and no `.` is read before the word (no lookbehind; the fit starts
# one char early after a char)
def shell_run() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Alt{[S.Begin{}], [S.Run{S.Cls{S.Codes{[S.Rg{46, 46}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, True{}, False{}}, 1n, Some{1n}}]}, S.Alt{[S.Lit{"bash"}], [S.Lit{"sh"}]}, S.Bound{}], False{}}

# 150 `\bnode\b`
def node_run() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Bound{}, S.Lit{"node"}, S.Bound{}], False{}}

# 151 `\b(?:cat|tee)\b.*(?:>|\s)(\S+)\s*<<-?`
def cat_write() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Bound{}, S.Alt{[S.Lit{"cat"}], [S.Lit{"tee"}]}, S.Bound{}, S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 0n, None{}}, S.Alt{[S.Lit{">"}], [S.Run{S.Cls{S.Space{}, False{}, False{}}, 1n, Some{1n}}]}, S.Cap{[S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}]}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}, S.Lit{"<<"}, S.Opt{[S.Lit{"-"}]}], False{}}

# 152 `\bapply_patch\b`
def apply_patch() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Bound{}, S.Lit{"apply_patch"}, S.Bound{}], False{}}

# 153 `\b(?:rm|mv|cp|git{S}+(?:add|commit)|npm{S}+install|sed{S}+-i|perl{S}+-pi|tee|cat{S}*>|apply_patch)\b`
def mutation() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Bound{}, S.Alt{[S.Lit{"rm"}], [S.Alt{[S.Lit{"mv"}], [S.Alt{[S.Lit{"cp"}], [S.Alt{[S.Lit{"git"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Alt{[S.Lit{"add"}], [S.Lit{"commit"}]}], [S.Alt{[S.Lit{"npm"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Lit{"install"}], [S.Alt{[S.Lit{"sed"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Lit{"-i"}], [S.Alt{[S.Lit{"perl"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Lit{"-pi"}], [S.Alt{[S.Lit{"tee"}], [S.Alt{[S.Lit{"cat"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{">"}], [S.Lit{"apply_patch"}]}]}]}]}]}]}]}]}]}, S.Bound{}], False{}}

# 154 `^{S}*(?:import{S}+\S|from{S}+\S+{S}+import{S}+)`
def import_line() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Alt{[S.Lit{"import"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, Some{1n}}], [S.Lit{"from"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Run{S.Cls{S.Space{}, True{}, False{}}, 1n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Lit{"import"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}]}], False{}}

# 155 `^{S}*`
def indent() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}], False{}}

# 156 `^{S}*(?:await{S}+)?[A-Za-z_][A-Za-z0-9_.]*{S}*\(`
def call() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Lit{"await"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}]}, S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{46, 46}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"("}], False{}}

# 157 `^{S}*(?:await{S}+)?(?:print|len|str|repr|int|float|list|dict|set|tuple){S}*\(`
def low_call() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Lit{"await"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}]}, S.Alt{[S.Lit{"print"}], [S.Alt{[S.Lit{"len"}], [S.Alt{[S.Lit{"str"}], [S.Alt{[S.Lit{"repr"}], [S.Alt{[S.Lit{"int"}], [S.Alt{[S.Lit{"float"}], [S.Alt{[S.Lit{"list"}], [S.Alt{[S.Lit{"dict"}], [S.Alt{[S.Lit{"set"}], [S.Lit{"tuple"}]}]}]}]}]}]}]}]}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"("}], False{}}

# 158 `^print\((.*)\)$`
def print_call() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Lit{"print("}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 0n, None{}}]}, S.Lit{")"}], True{}}

# 159 `^{S}*([A-Za-z_][A-Za-z0-9_]*){S}*={S}*(?:Path|pathlib\.Path)\((["'])([^"']+)\2\)`
def path_assign() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"="}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Alt{[S.Lit{"Path"}], [S.Lit{"pathlib.Path"}]}, S.Lit{"("}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, True{}, False{}}, 1n, None{}}]}, S.Same{2n}, S.Lit{")"}], False{}}

# 160 `^{S}*([A-Za-z_][A-Za-z0-9_]*){S}*={S}*(["'])([^"']+)\2`
def string_assign() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"="}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, True{}, False{}}, 1n, None{}}]}, S.Same{2n}], False{}}

# 161 `^(?:await\s+)?([A-Za-z_][A-Za-z0-9_]*)\.(write_text|write_bytes|read_text|read_bytes|mkdir|unlink|rename|replace|touch)\s*\(`
def file_op() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Opt{[S.Lit{"await"}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 1n, None{}}]}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}]}, S.Lit{"."}, S.Cap{[S.Alt{[S.Lit{"write_text"}], [S.Alt{[S.Lit{"write_bytes"}], [S.Alt{[S.Lit{"read_text"}], [S.Alt{[S.Lit{"read_bytes"}], [S.Alt{[S.Lit{"mkdir"}], [S.Alt{[S.Lit{"unlink"}], [S.Alt{[S.Lit{"rename"}], [S.Alt{[S.Lit{"replace"}], [S.Lit{"touch"}]}]}]}]}]}]}]}]}]}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}, S.Lit{"("}], False{}}

# 162 `subprocess\.(?:run|check_call|check_output|Popen)\(\s*(["`])([^"`]+)\1`
def subprocess_string() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Lit{"subprocess."}, S.Alt{[S.Lit{"run"}], [S.Alt{[S.Lit{"check_call"}], [S.Alt{[S.Lit{"check_output"}], [S.Lit{"Popen"}]}]}]}, S.Lit{"("}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{96, 96}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{96, 96}]}, True{}, False{}}, 1n, None{}}]}, S.Same{1n}], False{}}

# 163 `subprocess\.(?:run|check_call|check_output|Popen)\(\s*\[([^\]]+)\]`
def subprocess_list() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Lit{"subprocess."}, S.Alt{[S.Lit{"run"}], [S.Alt{[S.Lit{"check_call"}], [S.Alt{[S.Lit{"check_output"}], [S.Lit{"Popen"}]}]}]}, S.Lit{"("}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}, S.Lit{"["}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{93, 93}]}, True{}, False{}}, 1n, None{}}]}, S.Lit{"]"}], False{}}

# 164 `["']([^"']+)["']`
def quoted() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, True{}, False{}}, 1n, None{}}]}, S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}], False{}}

# 165 `^{S}*(?:async{S}+def|def|class){S}+`
def def_line() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Alt{[S.Lit{"async"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Lit{"def"}], [S.Alt{[S.Lit{"def"}], [S.Lit{"class"}]}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}], False{}}

# 166 `^{S}*@`
def decorator() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"@"}], False{}}

# 167 `^{S}*(?:if|elif|else|for|while|with|try|except|finally)\b.*:\s*$`
def compound() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Alt{[S.Lit{"if"}], [S.Alt{[S.Lit{"elif"}], [S.Alt{[S.Lit{"else"}], [S.Alt{[S.Lit{"for"}], [S.Alt{[S.Lit{"while"}], [S.Alt{[S.Lit{"with"}], [S.Alt{[S.Lit{"try"}], [S.Alt{[S.Lit{"except"}], [S.Lit{"finally"}]}]}]}]}]}]}]}]}, S.Bound{}, S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 0n, None{}}, S.Lit{":"}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}], True{}}

# 168 `:\s*$`
def colon_end() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Lit{":"}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}], True{}}

# 169 `^[)\]},;\s]+(?:#.*)?$`
def closers() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{133, 133}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{41, 41}, S.Rg{44, 44}, S.Rg{59, 59}, S.Rg{93, 93}, S.Rg{125, 125}]}, False{}, False{}}, 1n, None{}}, S.Opt{[S.Lit{"#"}, S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, True{}, False{}}, 0n, None{}}]}], True{}}

# 170 `^{S}*if{S}+__name__{S}*=={S}*['"]__main__['"]{S}*:`
def main_guard() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"if"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}, S.Lit{"__name__"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"=="}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}, S.Lit{"__main__"}, S.Run{S.Cls{S.Codes{[S.Rg{34, 34}, S.Rg{39, 39}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{":"}], False{}}

# 171 `^{S}*(?:await{S}+)?[A-Za-z_][A-Za-z0-9_.]*\.(?:write_text|write_bytes|mkdir|unlink|rename|replace|touch|append|extend|update|add|remove|discard|close|commit|execute|run){S}*\(`
def method_call() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Lit{"await"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}]}, S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{46, 46}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}, S.Lit{"."}, S.Alt{[S.Lit{"write_text"}], [S.Alt{[S.Lit{"write_bytes"}], [S.Alt{[S.Lit{"mkdir"}], [S.Alt{[S.Lit{"unlink"}], [S.Alt{[S.Lit{"rename"}], [S.Alt{[S.Lit{"replace"}], [S.Alt{[S.Lit{"touch"}], [S.Alt{[S.Lit{"append"}], [S.Alt{[S.Lit{"extend"}], [S.Alt{[S.Lit{"update"}], [S.Alt{[S.Lit{"add"}], [S.Alt{[S.Lit{"remove"}], [S.Alt{[S.Lit{"discard"}], [S.Alt{[S.Lit{"close"}], [S.Alt{[S.Lit{"commit"}], [S.Alt{[S.Lit{"execute"}], [S.Lit{"run"}]}]}]}]}]}]}]}]}]}]}]}]}]}]}]}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"("}], False{}}

# 172 `^{S}*[A-Za-z_][A-Za-z0-9_]*(?:{S}*:\s*[^=]+)?{S}*={S}*(?:await{S}+)?(?:Path|pathlib\.Path|json\.loads|json\.dumps|str|int|float|list|dict|set|tuple){S}*\(`
def value_assign() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{":"}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{61, 61}]}, True{}, False{}}, 1n, None{}}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"="}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Lit{"await"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}]}, S.Alt{[S.Lit{"Path"}], [S.Alt{[S.Lit{"pathlib.Path"}], [S.Alt{[S.Lit{"json.loads"}], [S.Alt{[S.Lit{"json.dumps"}], [S.Alt{[S.Lit{"str"}], [S.Alt{[S.Lit{"int"}], [S.Alt{[S.Lit{"float"}], [S.Alt{[S.Lit{"list"}], [S.Alt{[S.Lit{"dict"}], [S.Alt{[S.Lit{"set"}], [S.Lit{"tuple"}]}]}]}]}]}]}]}]}]}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"("}], False{}}

# 173 `^{S}*[A-Za-z_][A-Za-z0-9_]*(?:{S}*:\s*[^=]+)?{S}*={S}*(?:await{S}+)?[A-Za-z_][A-Za-z0-9_.]*{S}*\(`
def call_assign() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{":"}, S.Run{S.Cls{S.Space{}, False{}, False{}}, 0n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{61, 61}]}, True{}, False{}}, 1n, None{}}]}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"="}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Lit{"await"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}]}, S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{46, 46}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"("}], False{}}

# 174 `{S}*(?:[A-Za-z_][A-Za-z0-9_]*{S}*={S}*)?(?:await{S}+)?bash{S}*\({S}*[rR]?("""|'''|"|')`
def bash_call() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 1n, Some{1n}}, S.Run{S.Cls{S.Codes{[S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{95, 95}, S.Rg{97, 122}]}, False{}, False{}}, 0n, None{}}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"="}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}]}, S.Opt{[S.Lit{"await"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 1n, None{}}]}, S.Lit{"bash"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Lit{"("}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{82, 82}, S.Rg{114, 114}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Cap{[S.Alt{[S.Lit{"\"\"\""}], [S.Alt{[S.Lit{"'''"}], [S.Alt{[S.Lit{"\""}], [S.Lit{"'"}]}]}]}]}], False{}}

# 175 `^({S}*);{S}*`
def semicolon() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}]}, S.Lit{";"}, S.Run{S.Cls{S.Codes{[S.Rg{9, 13}, S.Rg{32, 32}, S.Rg{160, 160}, S.Rg{5760, 5760}, S.Rg{8192, 8202}, S.Rg{8232, 8233}, S.Rg{8239, 8239}, S.Rg{8287, 8287}, S.Rg{12288, 12288}, S.Rg{65279, 65279}]}, False{}, False{}}, 0n, None{}}], False{}}

# 176 cell.rs `bash_cell_magic_match`, a hand port of TS
# `^(?:[ \t]*\r?\n)*[ \t]*%%bash\b[^\r\n]*(?:\r?\n|$)`; as ported, a lone
def bash_magic() -> S.Shape:
  S.Shape{S.AtStart{}, [S.Many{[S.Run{S.Cls{S.Codes{[S.Rg{9, 9}, S.Rg{32, 32}]}, False{}, False{}}, 0n, None{}}, S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{13, 13}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, False{}, False{}}, 1n, Some{1n}}], 0n}, S.Run{S.Cls{S.Codes{[S.Rg{9, 9}, S.Rg{32, 32}]}, False{}, False{}}, 0n, None{}}, S.Lit{"%%bash"}, S.Bound{}, S.Run{S.Cls{S.Codes{[S.Rg{10, 10}, S.Rg{13, 13}]}, True{}, False{}}, 0n, None{}}, S.Opt{[S.Opt{[S.Run{S.Cls{S.Codes{[S.Rg{13, 13}]}, False{}, False{}}, 1n, Some{1n}}]}, S.Run{S.Cls{S.Codes{[S.Rg{10, 10}]}, False{}, False{}}, 1n, Some{1n}}]}], False{}}

# The table: the shape of id 130 + i at index i (none past the last)
def shape(i: Nat) -> Maybe<&2, S.Shape>:
  match i:
    case 0n:
      Some{ws_run()}
    case 1n:
      Some{blob()}
    case 2n:
      Some{secret_quoted()}
    case 3n:
      Some{secret_bare()}
    case 4n:
      Some{authorization()}
    case 5n:
      Some{sk_key()}
    case 6n:
      Some{long_string()}
    case 7n:
      Some{magic()}
    case 8n:
      Some{cd_prefix()}
    case 9n:
      Some{comment()}
    case 10n:
      Some{set_line()}
    case 11n:
      Some{env_line()}
    case 12n:
      Some{shell_word()}
    case 13n:
      Some{dot_slash()}
    case 14n:
      Some{vitest_cli()}
    case 15n:
      Some{bin_prefix()}
    case 16n:
      Some{chain_sep()}
    case 17n:
      Some{heredoc()}
    case 18n:
      Some{python_run()}
    case 19n:
      Some{shell_run()}
    case 20n:
      Some{node_run()}
    case 21n:
      Some{cat_write()}
    case 22n:
      Some{apply_patch()}
    case 23n:
      Some{mutation()}
    case 24n:
      Some{import_line()}
    case 25n:
      Some{indent()}
    case 26n:
      Some{call()}
    case 27n:
      Some{low_call()}
    case 28n:
      Some{print_call()}
    case 29n:
      Some{path_assign()}
    case 30n:
      Some{string_assign()}
    case 31n:
      Some{file_op()}
    case 32n:
      Some{subprocess_string()}
    case 33n:
      Some{subprocess_list()}
    case 34n:
      Some{quoted()}
    case 35n:
      Some{def_line()}
    case 36n:
      Some{decorator()}
    case 37n:
      Some{compound()}
    case 38n:
      Some{colon_end()}
    case 39n:
      Some{closers()}
    case 40n:
      Some{main_guard()}
    case 41n:
      Some{method_call()}
    case 42n:
      Some{value_assign()}
    case 43n:
      Some{call_assign()}
    case 44n:
      Some{bash_call()}
    case 45n:
      Some{semicolon()}
    case 46n:
      Some{bash_magic()}
    case 47n+k:
      None{}


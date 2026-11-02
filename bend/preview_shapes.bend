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
# intended difference). Pure: no IO, no @unsafe.

import Base
import ./shape.bend as S

# Classes
# -------

def rg(+x: U32) -> S.Rg:
  S.Rg{x, x}

# JS `\s` (bash.rs `S`): 9-13, space, U+00A0, U+1680, U+2000-U+200A,
# U+2028, U+2029, U+202F, U+205F, U+3000, U+FEFF
def js_rgs() -> List<&2, S.Rg>:
  [S.Rg{9, 13}, rg(32), rg(160), rg(5760), S.Rg{8192, 8202}, S.Rg{8232, 8233}, rg(8239), rg(8287), rg(12288), rg(65279)]

# Unicode White_Space (regex `\s`): 9-13, space, U+0085, U+00A0, U+1680,
# U+2000-U+200A, U+2028, U+2029, U+202F, U+205F, U+3000
def ws_rgs() -> List<&2, S.Rg>:
  [S.Rg{9, 13}, rg(32), rg(133), rg(160), rg(5760), S.Rg{8192, 8202}, S.Rg{8232, 8233}, rg(8239), rg(8287), rg(12288)]

def cls(rs: List<&2, S.Rg>) -> S.Cls:
  S.Cls{S.Codes{rs}, False{}, False{}}

def but(rs: List<&2, S.Rg>) -> S.Cls:
  S.Cls{S.Codes{rs}, True{}, False{}}

# `{S}`
def js() -> S.Cls:
  cls(js_rgs())

# `\s`, `\S`
def ws() -> S.Cls:
  S.Cls{S.Space{}, False{}, False{}}

def nws() -> S.Cls:
  S.Cls{S.Space{}, True{}, False{}}

# `{W}`: `[A-Za-z0-9_]`
def word() -> S.Cls:
  cls([S.Rg{48, 57}, S.Rg{65, 90}, rg(95), S.Rg{97, 122}])

# `[A-Za-z_]`
def head() -> S.Cls:
  cls([S.Rg{65, 90}, rg(95), S.Rg{97, 122}])

# `[A-Za-z0-9_.]`
def dotted() -> S.Cls:
  cls([rg(46), S.Rg{48, 57}, S.Rg{65, 90}, rg(95), S.Rg{97, 122}])

# `["']`, `[^"']`
def quote() -> S.Cls:
  cls([rg(34), rg(39)])

def no_quote() -> S.Cls:
  but([rg(34), rg(39)])

# `.`: any char but a line feed
def dot() -> S.Cls:
  but([rg(10)])

def one(c: S.Cls) -> S.Piece:
  S.Run{c, 1n, Some{1n}}

def plus(c: S.Cls) -> S.Piece:
  S.Run{c, 1n, None{}}

def star(c: S.Cls) -> S.Piece:
  S.Run{c, 0n, None{}}

# `[A-Za-z_][A-Za-z0-9_]*`: a name
def name() -> List<&2, S.Piece>:
  [one(head()), star(word())]

# `(?:await{S}+)?`
def awaited() -> S.Piece:
  S.Opt{[S.Lit{"await"}, plus(js())]}

# A lookup builds its shape on every call, so the helpers below build each
# choice as one piece in place (no list is appended).

# the words, one of them, the first tried first (`a|b|c`)
def words.go(t: List<&2, String>, w: String) -> List<&2, S.Piece>:
  match t:
    case Nil{}:
      [S.Lit{w}]
    case u <> r:
      [S.Alt{[S.Lit{w}], words.go(r, u)}]

# `w|v|...t`: one of two or more words
def either(w: String, v: String, t: List<&2, String>) -> S.Piece:
  S.Alt{[S.Lit{w}], words.go(t, v)}

# the same, ASCII letters in either case (`(?i)a|b|c`)
def fwords.go(t: List<&2, String>, w: String) -> List<&2, S.Piece>:
  match t:
    case Nil{}:
      [S.Fold{w}]
    case u <> r:
      [S.Alt{[S.Fold{w}], fwords.go(r, u)}]

def feither(w: String, v: String, t: List<&2, String>) -> S.Piece:
  S.Alt{[S.Fold{w}], fwords.go(t, v)}

# the options, one of them, the first tried first (`a|b|c`)
def alts.go(t: List<&2, List<&2, S.Piece>>, a: List<&2, S.Piece>) -> List<&2, S.Piece>:
  match t:
    case Nil{}:
      a
    case b <> r:
      [S.Alt{a, alts.go(r, b)}]

# `a|b|...t`: one of two or more options
def either_of(a: List<&2, S.Piece>, b: List<&2, S.Piece>, t: List<&2, List<&2, S.Piece>>) -> S.Piece:
  S.Alt{a, alts.go(t, b)}

def at_start(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.AtStart{}, ps, False{}}

def whole(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.AtStart{}, ps, True{}}

def anywhere(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.Anywhere{}, ps, False{}}

def anywhere_end(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.Anywhere{}, ps, True{}}

# a secret word (`(?i)` when fold)
def secret_word(fold: Bool) -> S.Piece:
  match fold:
    case True{}:
      feither("token", "key", ["secret", "password"])
    case False{}:
      either("token", "key", ["secret", "password"])

# `(?=[A-Za-z0-9_]*(?:token|key|secret|password))[A-Za-z_][A-Za-z0-9_]*`
# (`(?i)` when fold): a name holding a secret word
def secret_name(fold: Bool) -> S.Piece:
  S.Cap{[S.Ahead{[star(word()), secret_word(fold)], False{}}, one(head()), star(word())]}

# The shapes (bash.rs)
# --------------------

# 130 `{S}+`
def ws_run() -> S.Shape:
  anywhere([plus(js())])

# 131 `[A-Za-z0-9+/]{80,}={0,2}`
def blob() -> S.Shape:
  anywhere([S.Run{cls([rg(43), rg(47), S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]), 80n, None{}}, S.Run{cls([rg(61)]), 0n, Some{2n}}])

# 132 `\b((?={W}*(?:token|key|secret|password))[A-Za-z_]{W}*){S}*={S}*(["'])[^"']*\2`
def secret_quoted() -> S.Shape:
  anywhere([S.Bound{}, secret_name(False{}), star(js()), S.Lit{"="}, star(js()), S.Cap{[one(quote())]}, star(no_quote()), S.Same{2n}])

# 133 `(?i)\b((?={W}*(?:token|key|secret|password))[A-Za-z_]{W}*){S}*={S}*(?!<redacted>)(?!["'])\S+`
def secret_bare() -> S.Shape:
  anywhere([S.Bound{}, secret_name(True{}), star(js()), S.Lit{"="}, star(js()), S.Ahead{[S.Fold{"<redacted>"}], True{}}, S.Ahead{[one(quote())], True{}}, plus(nws())])

# 134 `(?i)\b(authorization:\s*(?:bearer\s+)?)[^\s"']+`
def authorization() -> S.Shape:
  anywhere([S.Bound{}, S.Cap{[S.Fold{"authorization:"}, star(ws()), S.Opt{[S.Fold{"bearer"}, plus(ws())]}]}, plus(but(List.append(&2, S.Rg, ws_rgs(), [rg(34), rg(39)])))])

# 135 `(["'])sk-[^"']+\1`
def sk_key() -> S.Shape:
  anywhere([S.Cap{[one(quote())]}, S.Lit{"sk-"}, plus(no_quote()), S.Same{1n}])

# 136 `(["']).{160,}\1`
def long_string() -> S.Shape:
  anywhere([S.Cap{[one(quote())]}, S.Run{dot(), 160n, None{}}, S.Same{1n}])

# 137 `^{S}*!`
def magic() -> S.Shape:
  at_start([star(js()), S.Lit{"!"}])

# 138 `^{S}*cd{S}+([^&;|]+)(?:&&|;){S}*`
def cd_prefix() -> S.Shape:
  at_start([star(js()), S.Lit{"cd"}, plus(js()), S.Cap{[plus(but([rg(38), rg(59), rg(124)]))]}, S.Alt{[S.Lit{"&&"}], [S.Lit{";"}]}, star(js())])

# 139 `^{S}*#`
def comment() -> S.Shape:
  at_start([star(js()), S.Lit{"#"}])

# 140 `^{S}*set{S}+[-+][A-Za-z]*(?:{S}+[-+]?{W}+)*(?:{S}+pipefail)?{S}*$`
def set_line() -> S.Shape:
  whole([star(js()), S.Lit{"set"}, plus(js()), one(cls([rg(43), rg(45)])), star(cls([S.Rg{65, 90}, S.Rg{97, 122}])), S.Many{[plus(js()), S.Opt{[one(cls([rg(43), rg(45)]))]}, plus(word())], 0n}, S.Opt{[plus(js()), S.Lit{"pipefail"}]}, star(js())])

# 141 `^(?:export{S}+{W}+=|source{S}+\S+|\.{S}+\S+)`
def env_line() -> S.Shape:
  at_start([either_of([S.Lit{"export"}, plus(js()), plus(word()), S.Lit{"="}], [S.Lit{"source"}, plus(js()), plus(nws())], [[S.Lit{"."}, plus(js()), plus(nws())]])])

# 142 `"([^"]*)"|'([^']*)'|(\S+)`
def shell_word() -> S.Shape:
  anywhere([either_of([S.Lit{"\""}, S.Cap{[star(but([rg(34)]))]}, S.Lit{"\""}], [S.Lit{"'"}, S.Cap{[star(but([rg(39)]))]}, S.Lit{"'"}], [[S.Cap{[plus(nws())]}]])])

# 143 `^\./`
def dot_slash() -> S.Shape:
  at_start([S.Lit{"./"}])

# 144 `(?:^|/)vitest/dist/cli\.js$`
def vitest_cli() -> S.Shape:
  anywhere_end([S.Alt{[S.Begin{}], [S.Lit{"/"}]}, S.Lit{"vitest/dist/cli.js"}])

# 145 `\S*node_modules/\.bin/`
def bin_prefix() -> S.Shape:
  anywhere([star(nws()), S.Lit{"node_modules/.bin/"}])

# 146 `\s*(?:&&|;)\s*`
def chain_sep() -> S.Shape:
  anywhere([star(ws()), S.Alt{[S.Lit{"&&"}], [S.Lit{";"}]}, star(ws())])

# 147 `<<-?\s*['"]?([A-Za-z_][A-Za-z0-9_]*)['"]?`
def heredoc() -> S.Shape:
  anywhere([S.Lit{"<<"}, S.Opt{[S.Lit{"-"}]}, star(ws()), S.Opt{[one(quote())]}, S.Cap{name()}, S.Opt{[one(quote())]}])

# 148 `\b(?:uv{S}+run{S}+)?python3?\b`
def python_run() -> S.Shape:
  anywhere([S.Bound{}, S.Opt{[S.Lit{"uv"}, plus(js()), S.Lit{"run"}, plus(js())]}, S.Lit{"python"}, S.Opt{[S.Lit{"3"}]}, S.Bound{}])

# 149 `(?<![\w.])(?:bash|sh)\b`: the text start or a char that is no word
# char and no `.` is read before the word (no lookbehind; the fit starts
# one char early after a char)
def shell_run() -> S.Shape:
  anywhere([S.Alt{[S.Begin{}], [one(but([rg(46), S.Rg{48, 57}, S.Rg{65, 90}, rg(95), S.Rg{97, 122}]))]}, S.Alt{[S.Lit{"bash"}], [S.Lit{"sh"}]}, S.Bound{}])

# 150 `\bnode\b`
def node_run() -> S.Shape:
  anywhere([S.Bound{}, S.Lit{"node"}, S.Bound{}])

# 151 `\b(?:cat|tee)\b.*(?:>|\s)(\S+)\s*<<-?`
def cat_write() -> S.Shape:
  anywhere([S.Bound{}, S.Alt{[S.Lit{"cat"}], [S.Lit{"tee"}]}, S.Bound{}, star(dot()), S.Alt{[S.Lit{">"}], [one(ws())]}, S.Cap{[plus(nws())]}, star(ws()), S.Lit{"<<"}, S.Opt{[S.Lit{"-"}]}])

# 152 `\bapply_patch\b`
def apply_patch() -> S.Shape:
  anywhere([S.Bound{}, S.Lit{"apply_patch"}, S.Bound{}])

# 153 `\b(?:rm|mv|cp|git{S}+(?:add|commit)|npm{S}+install|sed{S}+-i|perl{S}+-pi|tee|cat{S}*>|apply_patch)\b`
def mutation() -> S.Shape:
  anywhere([S.Bound{}, either_of([S.Lit{"rm"}], [S.Lit{"mv"}], [[S.Lit{"cp"}], [S.Lit{"git"}, plus(js()), S.Alt{[S.Lit{"add"}], [S.Lit{"commit"}]}], [S.Lit{"npm"}, plus(js()), S.Lit{"install"}], [S.Lit{"sed"}, plus(js()), S.Lit{"-i"}], [S.Lit{"perl"}, plus(js()), S.Lit{"-pi"}], [S.Lit{"tee"}], [S.Lit{"cat"}, star(js()), S.Lit{">"}], [S.Lit{"apply_patch"}]]), S.Bound{}])

# The shapes (python.rs)
# ----------------------

# 154 `^{S}*(?:import{S}+\S|from{S}+\S+{S}+import{S}+)`
def import_line() -> S.Shape:
  at_start([star(js()), S.Alt{[S.Lit{"import"}, plus(js()), one(nws())], [S.Lit{"from"}, plus(js()), plus(nws()), plus(js()), S.Lit{"import"}, plus(js())]}])

# 155 `^{S}*`
def indent() -> S.Shape:
  at_start([star(js())])

# 156 `^{S}*(?:await{S}+)?[A-Za-z_][A-Za-z0-9_.]*{S}*\(`
def call() -> S.Shape:
  at_start([star(js()), awaited(), one(head()), star(dotted()), star(js()), S.Lit{"("}])

# 157 `^{S}*(?:await{S}+)?(?:print|len|str|repr|int|float|list|dict|set|tuple){S}*\(`
def low_call() -> S.Shape:
  at_start([star(js()), awaited(), either("print", "len", ["str", "repr", "int", "float", "list", "dict", "set", "tuple"]), star(js()), S.Lit{"("}])

# 158 `^print\((.*)\)$`
def print_call() -> S.Shape:
  whole([S.Lit{"print("}, S.Cap{[star(dot())]}, S.Lit{")"}])

# 159 `^{S}*([A-Za-z_][A-Za-z0-9_]*){S}*={S}*(?:Path|pathlib\.Path)\((["'])([^"']+)\2\)`
def path_assign() -> S.Shape:
  at_start([star(js()), S.Cap{name()}, star(js()), S.Lit{"="}, star(js()), S.Alt{[S.Lit{"Path"}], [S.Lit{"pathlib.Path"}]}, S.Lit{"("}, S.Cap{[one(quote())]}, S.Cap{[plus(no_quote())]}, S.Same{2n}, S.Lit{")"}])

# 160 `^{S}*([A-Za-z_][A-Za-z0-9_]*){S}*={S}*(["'])([^"']+)\2`
def string_assign() -> S.Shape:
  at_start([star(js()), S.Cap{name()}, star(js()), S.Lit{"="}, star(js()), S.Cap{[one(quote())]}, S.Cap{[plus(no_quote())]}, S.Same{2n}])

# 161 `^(?:await\s+)?([A-Za-z_][A-Za-z0-9_]*)\.(write_text|write_bytes|read_text|read_bytes|mkdir|unlink|rename|replace|touch)\s*\(`
def file_op() -> S.Shape:
  at_start([S.Opt{[S.Lit{"await"}, plus(ws())]}, S.Cap{name()}, S.Lit{"."}, S.Cap{[either("write_text", "write_bytes", ["read_text", "read_bytes", "mkdir", "unlink", "rename", "replace", "touch"])]}, star(ws()), S.Lit{"("}])

# `subprocess\.(?:run|check_call|check_output|Popen)`
def subprocess() -> S.Piece:
  either("run", "check_call", ["check_output", "Popen"])

# 162 `subprocess\.(?:run|check_call|check_output|Popen)\(\s*(["`])([^"`]+)\1`
def subprocess_string() -> S.Shape:
  anywhere([S.Lit{"subprocess."}, subprocess(), S.Lit{"("}, star(ws()), S.Cap{[one(cls([rg(34), rg(96)]))]}, S.Cap{[plus(but([rg(34), rg(96)]))]}, S.Same{1n}])

# 163 `subprocess\.(?:run|check_call|check_output|Popen)\(\s*\[([^\]]+)\]`
def subprocess_list() -> S.Shape:
  anywhere([S.Lit{"subprocess."}, subprocess(), S.Lit{"("}, star(ws()), S.Lit{"["}, S.Cap{[plus(but([rg(93)]))]}, S.Lit{"]"}])

# 164 `["']([^"']+)["']`
def quoted() -> S.Shape:
  anywhere([one(quote()), S.Cap{[plus(no_quote())]}, one(quote())])

# 165 `^{S}*(?:async{S}+def|def|class){S}+`
def def_line() -> S.Shape:
  at_start([star(js()), either_of([S.Lit{"async"}, plus(js()), S.Lit{"def"}], [S.Lit{"def"}], [[S.Lit{"class"}]]), plus(js())])

# 166 `^{S}*@`
def decorator() -> S.Shape:
  at_start([star(js()), S.Lit{"@"}])

# 167 `^{S}*(?:if|elif|else|for|while|with|try|except|finally)\b.*:\s*$`
def compound() -> S.Shape:
  whole([star(js()), either("if", "elif", ["else", "for", "while", "with", "try", "except", "finally"]), S.Bound{}, star(dot()), S.Lit{":"}, star(ws())])

# 168 `:\s*$`
def colon_end() -> S.Shape:
  anywhere_end([S.Lit{":"}, star(ws())])

# 169 `^[)\]},;\s]+(?:#.*)?$`
def closers() -> S.Shape:
  whole([plus(cls(List.append(&2, S.Rg, ws_rgs(), [rg(41), rg(44), rg(59), rg(93), rg(125)]))), S.Opt{[S.Lit{"#"}, star(dot())]}])

# 170 `^{S}*if{S}+__name__{S}*=={S}*['"]__main__['"]{S}*:`
def main_guard() -> S.Shape:
  at_start([star(js()), S.Lit{"if"}, plus(js()), S.Lit{"__name__"}, star(js()), S.Lit{"=="}, star(js()), one(quote()), S.Lit{"__main__"}, one(quote()), star(js()), S.Lit{":"}])

# 171 `^{S}*(?:await{S}+)?[A-Za-z_][A-Za-z0-9_.]*\.(?:write_text|write_bytes|mkdir|unlink|rename|replace|touch|append|extend|update|add|remove|discard|close|commit|execute|run){S}*\(`
def method_call() -> S.Shape:
  at_start([star(js()), awaited(), one(head()), star(dotted()), S.Lit{"."}, either("write_text", "write_bytes", ["mkdir", "unlink", "rename", "replace", "touch", "append", "extend", "update", "add", "remove", "discard", "close", "commit", "execute", "run"]), star(js()), S.Lit{"("}])

# `(?:{S}*:\s*[^=]+)?`: a type annotation, or nothing
def annotation() -> S.Piece:
  S.Opt{[star(js()), S.Lit{":"}, star(ws()), plus(but([rg(61)]))]}

# 172 `^{S}*[A-Za-z_][A-Za-z0-9_]*(?:{S}*:\s*[^=]+)?{S}*={S}*(?:await{S}+)?(?:Path|pathlib\.Path|json\.loads|json\.dumps|str|int|float|list|dict|set|tuple){S}*\(`
def value_assign() -> S.Shape:
  at_start([star(js()), one(head()), star(word()), annotation(), star(js()), S.Lit{"="}, star(js()), awaited(), either("Path", "pathlib.Path", ["json.loads", "json.dumps", "str", "int", "float", "list", "dict", "set", "tuple"]), star(js()), S.Lit{"("}])

# 173 `^{S}*[A-Za-z_][A-Za-z0-9_]*(?:{S}*:\s*[^=]+)?{S}*={S}*(?:await{S}+)?[A-Za-z_][A-Za-z0-9_.]*{S}*\(`
def call_assign() -> S.Shape:
  at_start([star(js()), one(head()), star(word()), annotation(), star(js()), S.Lit{"="}, star(js()), awaited(), one(head()), star(dotted()), star(js()), S.Lit{"("}])

# 174 `{S}*(?:[A-Za-z_][A-Za-z0-9_]*{S}*={S}*)?(?:await{S}+)?bash{S}*\({S}*[rR]?("""|'''|"|')`
def bash_call() -> S.Shape:
  anywhere([star(js()), S.Opt{[one(head()), star(word()), star(js()), S.Lit{"="}, star(js())]}, awaited(), S.Lit{"bash"}, star(js()), S.Lit{"("}, star(js()), S.Opt{[one(cls([rg(82), rg(114)]))]}, S.Cap{[either("\"\"\"", "'''", ["\"", "'"])]}])

# 175 `^({S}*);{S}*`
def semicolon() -> S.Shape:
  at_start([S.Cap{[star(js())]}, S.Lit{";"}, star(js())])

# The shape (cell.rs)
# -------------------

# 176 cell.rs `bash_cell_magic_match`, a hand port of TS
# `^(?:[ \t]*\r?\n)*[ \t]*%%bash\b[^\r\n]*(?:\r?\n|$)`; as ported, a lone
# CR after the magic line ends the fit unread (the TS regex fails there)
def bash_magic() -> S.Shape:
  at_start([S.Many{[star(cls([rg(9), rg(32)])), S.Opt{[one(cls([rg(13)]))]}, one(cls([rg(10)]))], 0n}, star(cls([rg(9), rg(32)])), S.Lit{"%%bash"}, S.Bound{}, star(but([rg(10), rg(13)])), S.Opt{[S.Opt{[one(cls([rg(13)]))]}, one(cls([rg(10)]))]}])

# The table: the shape of id 130 + i at index i (none past the last); a
# lookup builds only the shape it answers
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

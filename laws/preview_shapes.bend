# eukhe: the laws of area preview_shapes

import Base
import ../bend/shape.bend as S
import ../bend/preview_shapes.bend as PS

# (PV1) The shapes the code preview reads
# ---------------------------------------
# bend/preview_shapes.bend, ids 130-199 of the entry bend/ffi_shape.bend
# (eukhe-tui code_preview/bash.rs, python.rs and cell.rs ask them through
# eukhe-tui text_shapes.rs, in place of their regexes). The matcher is
# pinned by laws/shape/match.bend and laws/shape/search.bend.
# "a JS blank" is a char of JS `\s`: 9-13, space, U+00A0, U+1680,
# U+2000-U+200A, U+2028, U+2029, U+202F, U+205F, U+3000, U+FEFF; "JS
# blanks" any number of them (none too), "a JS blank run" one or more.
# "White_Space" is Unicode White_Space: 9-13, space, U+0085, U+00A0,
# U+1680, U+2000-U+200A, U+2028, U+2029, U+202F, U+205F, U+3000; "a dark
# char" a char that is no White_Space. "a word char" is an ASCII letter,
# an ASCII digit or `_`; "a name" a letter or `_`, then word chars (none
# too); "a quote" `"` or `'`; "the rest of the line" chars that are no line
# feed. "at a boundary" means a word char on one side and none (or the
# text edge) on the other (Rust's `\b` and `\w` are Unicode, JS's ASCII:
# an intended difference); "in either case" folds ASCII letters only
# (Rust's `(?i)` also takes the Kelvin sign and the long s: an intended
# difference). "one of a, b, c" tries them in that order. "the line is" a
# shape read at the text start that must end the text; "the line starts
# with" one read at the text start; "the text holds" one read at the
# leftmost place it fits; "the text ends with" one read at the leftmost
# place it fits that must end the text. Captures are numbered in order
# from 1. A class lists its blank or White_Space ranges first, then its
# other codes, each part from the lowest code up.
#
# R1: id 130: the text holds a JS blank run.
# R2: id 131, a blob: the text holds 80 or more chars, each an ASCII
#     letter, digit, `+` or `/`, then up to two `=`.
# R3: id 132, a quoted secret: the text holds, at a boundary, a name whose
#     word chars from its start hold `token`, `key`, `secret` or `password`
#     (captured: the name), JS blanks, `=`, JS blanks, a quote (captured),
#     chars that are no quote (none too), then that same quote.
# R4: id 133, a bare secret: the text holds, at a boundary, a name whose
#     word chars from its start hold `token`, `key`, `secret` or
#     `password` in either case (captured: the name), JS blanks, `=`, JS
#     blanks, then, where neither `<redacted>` in either case nor a quote
#     comes next, one or more dark chars.
# R5: id 134, an authorization header: the text holds, at a boundary,
#     `authorization:` in either case, White_Space (none too), then
#     `bearer` in either case and one or more White_Space, or nothing (all
#     of it captured), then one or more chars that are no White_Space and
#     no quote.
# R6: id 135, an sk- key: the text holds a quote (captured), `sk-`, one or
#     more chars that are no quote, then that same quote.
# R7: id 136, a long string: the text holds a quote (captured), 160 or more
#     chars of the rest of the line, then that same quote.
# R8: id 137, a magic: the line starts with JS blanks, `!`.
# R9: id 138, a cd prefix: the line starts with JS blanks, `cd`, a JS blank
#     run, one or more chars none of `&`, `;` and `|` (captured: the dir),
#     `&&` or `;`, JS blanks.
# R10: id 139, a comment: the line starts with JS blanks, `#`.
# R11: id 140, a set line: the line is JS blanks, `set`, a JS blank run,
#     `+` or `-`, ASCII letters (none too), then any number of rounds of a
#     JS blank run, `+`, `-` or nothing, and one or more word chars; then a
#     JS blank run and `pipefail`, or nothing; then JS blanks.
# R12: id 141, an environment line: the line starts with one of `export`,
#     a JS blank run, one or more word chars, `=`; `source`, a JS blank
#     run, one or more dark chars; `.`, a JS blank run, one or more dark
#     chars.
# R13: id 142, a shell word: the text holds one of `"`, chars that are no
#     `"` (none too; captured), `"`; `'`, chars that are no `'` (none too;
#     captured), `'`; one or more dark chars (captured).
# R14: id 143: the line starts with `./`.
# R15: id 144, the vitest cli: the text ends with the text start or `/`,
#     then `vitest/dist/cli.js`.
# R16: id 145, a bin prefix: the text holds dark chars (none too), then
#     `node_modules/.bin/`.
# R17: id 146, a chain separator: the text holds White_Space (none too),
#     `&&` or `;`, White_Space (none too).
# R18: id 147, a heredoc opener: the text holds `<<`, `-` or nothing,
#     White_Space (none too), a quote or nothing, a name (captured: the
#     delimiter), a quote or nothing.
# R19: id 148, a python run: the text holds, at a boundary, `uv`, a JS
#     blank run, `run`, a JS blank run, or nothing; then `python`, `3` or
#     nothing, at a boundary.
# R20: id 149, a shell run: the text holds the text start or one char that
#     is no word char and no `.` (the fit starts at that char), then `bash`
#     or `sh`, at a boundary.
# R21: id 150: the text holds, at a boundary, `node`, at a boundary.
# R22: id 151, a cat or tee write: the text holds, at a boundary, `cat` or
#     `tee`, at a boundary, the rest of the line (none too), `>` or one
#     White_Space, one or more dark chars (captured: the target),
#     White_Space (none too), `<<`, `-` or nothing.
# R23: id 152: the text holds, at a boundary, `apply_patch`, at a boundary.
# R24: id 153, a mutation: the text holds, at a boundary, one of `rm`;
#     `mv`; `cp`; `git`, a JS blank run, `add` or `commit`; `npm`, a JS
#     blank run, `install`; `sed`, a JS blank run, `-i`; `perl`, a JS
#     blank run, `-pi`; `tee`; `cat`, JS blanks, `>`; `apply_patch`; then
#     at a boundary.
# R25: id 154, an import: the line starts with JS blanks, then `import`, a
#     JS blank run and one dark char, or `from`, a JS blank run, one or
#     more dark chars, a JS blank run, `import`, a JS blank run.
# R26: id 155, an indent: the line starts with JS blanks.
# R27: id 156, a call: the line starts with JS blanks, `await` and a JS
#     blank run or nothing, a letter or `_`, then chars each a word char or
#     `.` (none too), JS blanks, `(`.
# R28: id 157, a low-signal call: the line starts with JS blanks, `await`
#     and a JS blank run or nothing, one of `print`, `len`, `str`, `repr`,
#     `int`, `float`, `list`, `dict`, `set`, `tuple`, then JS blanks, `(`.
# R29: id 158, a print: the line is `print(`, the rest of the line (none
#     too; captured), `)`.
# R30: id 159, a path assignment: the line starts with JS blanks, a name
#     (captured), JS blanks, `=`, JS blanks, `Path` or `pathlib.Path`, `(`,
#     a quote (captured), one or more chars that are no quote (captured),
#     that same quote, `)`.
# R31: id 160, a string assignment: the line starts with JS blanks, a name
#     (captured), JS blanks, `=`, JS blanks, a quote (captured), one or
#     more chars that are no quote (captured), that same quote.
# R32: id 161, a file operation: the line starts with `await` and one or
#     more White_Space or nothing, a name (captured), `.`, one of
#     `write_text`, `write_bytes`, `read_text`, `read_bytes`, `mkdir`,
#     `unlink`, `rename`, `replace`, `touch` (captured), White_Space (none
#     too), `(`.
# R33: id 162, a subprocess string: the text holds `subprocess.`, one of
#     `run`, `check_call`, `check_output`, `Popen`, then `(`, White_Space
#     (none too), `"` or a backquote (captured), one or more chars none of
#     them (captured), that same char.
# R34: id 163, a subprocess list: the text holds `subprocess.`, one of
#     `run`, `check_call`, `check_output`, `Popen`, then `(`, White_Space
#     (none too), `[`, one or more chars that are no `]` (captured), `]`.
# R35: id 164, a quoted word: the text holds a quote, one or more chars
#     that are no quote (captured), a quote (either one).
# R36: id 165, a definition: the line starts with JS blanks, one of
#     `async`, a JS blank run, `def`; `def`; `class`; then a JS blank run.
# R37: id 166, a decorator: the line starts with JS blanks, `@`.
# R38: id 167, a compound statement: the line is JS blanks, one of `if`,
#     `elif`, `else`, `for`, `while`, `with`, `try`, `except`, `finally`,
#     at a boundary, the rest of the line (none too), `:`, White_Space
#     (none too).
# R39: id 168, a colon end: the text ends with `:`, White_Space (none
#     too).
# R40: id 169, closers: the line is one or more chars each White_Space,
#     `)`, `,`, `;`, `]` or `}`, then `#` and the rest of the line (none
#     too), or nothing.
# R41: id 170, a main guard: the line starts with JS blanks, `if`, a JS
#     blank run, `__name__`, JS blanks, `==`, JS blanks, a quote,
#     `__main__`, a quote, JS blanks, `:`.
# R42: id 171, a method call: the line starts with JS blanks, `await` and
#     a JS blank run or nothing, a letter or `_`, chars each a word char or
#     `.` (none too), `.`, one of `write_text`, `write_bytes`, `mkdir`,
#     `unlink`, `rename`, `replace`, `touch`, `append`, `extend`, `update`,
#     `add`, `remove`, `discard`, `close`, `commit`, `execute`, `run`, then
#     JS blanks, `(`.
# R43: id 172, a value assignment: the line starts with an assignment (JS
#     blanks, a letter or `_`, word chars (none too), then JS blanks, `:`,
#     White_Space (none too) and one or more chars that are no `=`, or
#     nothing; then JS blanks, `=`, JS blanks, `await` and a JS blank run
#     or nothing), then one of `Path`, `pathlib.Path`, `json.loads`,
#     `json.dumps`, `str`, `int`, `float`, `list`, `dict`, `set`, `tuple`,
#     then JS blanks, `(`.
# R44: id 173, a call assignment: the line starts with an assignment (as
#     in R43), a letter or `_`, chars each a word char or `.` (none too),
#     JS blanks, `(`.
# R45: id 174, a bash skill call: the text holds JS blanks, then a name,
#     JS blanks, `=`, JS blanks, or nothing; `await` and a JS blank run or
#     nothing; `bash`, JS blanks, `(`, JS blanks, `r` or `R` or nothing,
#     then one of three `"`, three `'`, `"`, `'` (captured).
# R46: id 175, a leading semicolon: the line starts with JS blanks
#     (captured), `;`, JS blanks.
# R47: id 176, a bash cell magic: the line starts with any number of
#     rounds of tabs and spaces (none too), a CR or nothing, and a line
#     feed; then tabs and spaces (none too), `%%bash`, at a boundary, chars
#     none of CR and line feed (none too), then a CR or nothing and a line
#     feed, or nothing.
# R48: the table holds exactly these shapes, the one of id 130 + i at
#     index i, and no other.

# Spec helpers
# ------------

def sp_r(+x: U32) -> S.Rg:
  S.Rg{x, x}

# a JS blank; White_Space
def sp_js() -> List<&2, S.Rg>:
  [S.Rg{9, 13}, sp_r(32), sp_r(160), sp_r(5760), S.Rg{8192, 8202}, S.Rg{8232, 8233}, sp_r(8239), sp_r(8287), sp_r(12288), sp_r(65279)]

def sp_white() -> List<&2, S.Rg>:
  [S.Rg{9, 13}, sp_r(32), sp_r(133), sp_r(160), sp_r(5760), S.Rg{8192, 8202}, S.Rg{8232, 8233}, sp_r(8239), sp_r(8287), sp_r(12288)]

def sp_in(rs: List<&2, S.Rg>) -> S.Cls:
  S.Cls{S.Codes{rs}, False{}, False{}}

def sp_not(rs: List<&2, S.Rg>) -> S.Cls:
  S.Cls{S.Codes{rs}, True{}, False{}}

def sp_blank() -> S.Cls:
  sp_in(sp_js())

def sp_space() -> S.Cls:
  S.Cls{S.Space{}, False{}, False{}}

def sp_dark() -> S.Cls:
  S.Cls{S.Space{}, True{}, False{}}

# a word char; a letter or `_`; a word char or `.`
def sp_wordc() -> S.Cls:
  sp_in([S.Rg{48, 57}, S.Rg{65, 90}, sp_r(95), S.Rg{97, 122}])

def sp_lead() -> S.Cls:
  sp_in([S.Rg{65, 90}, sp_r(95), S.Rg{97, 122}])

def sp_dotted() -> S.Cls:
  sp_in([sp_r(46), S.Rg{48, 57}, S.Rg{65, 90}, sp_r(95), S.Rg{97, 122}])

# a quote; no quote; no line feed
def sp_q() -> S.Cls:
  sp_in([sp_r(34), sp_r(39)])

def sp_nq() -> S.Cls:
  sp_not([sp_r(34), sp_r(39)])

def sp_nolf() -> S.Cls:
  sp_not([sp_r(10)])

def sp_1(c: S.Cls) -> S.Piece:
  S.Run{c, 1n, Some{1n}}

def sp_some(c: S.Cls) -> S.Piece:
  S.Run{c, 1n, None{}}

def sp_any(c: S.Cls) -> S.Piece:
  S.Run{c, 0n, None{}}

def sp_t(s: String) -> S.Piece:
  S.Lit{s}

def sp_or_none(ps: List<&2, S.Piece>) -> S.Piece:
  S.Opt{ps}

# a name
def sp_name() -> List<&2, S.Piece>:
  [sp_1(sp_lead()), sp_any(sp_wordc())]

# `await` and a JS blank run, or nothing
def sp_await() -> S.Piece:
  sp_or_none([sp_t("await"), sp_some(sp_blank())])

# one of the options, in order
def sp_one_of.go(t: List<&2, List<&2, S.Piece>>, a: List<&2, S.Piece>) -> List<&2, S.Piece>:
  match t:
    case Nil{}:
      a
    case b <> r:
      [S.Alt{a, sp_one_of.go(r, b)}]

def sp_one_of(xs: List<&2, List<&2, S.Piece>>) -> List<&2, S.Piece>:
  match xs:
    case Nil{}:
      Nil{}
    case a <> t:
      sp_one_of.go(t, a)

def sp_lits(xs: List<&2, String>) -> List<&2, List<&2, S.Piece>>:
  match xs:
    case Nil{}:
      Nil{}
    case w <> t:
      [S.Lit{w}] <> sp_lits(t)

def sp_folds(xs: List<&2, String>) -> List<&2, List<&2, S.Piece>>:
  match xs:
    case Nil{}:
      Nil{}
    case w <> t:
      [S.Fold{w}] <> sp_folds(t)

def sp_words(xs: List<&2, String>) -> List<&2, S.Piece>:
  sp_one_of(sp_lits(xs))

def sp_cat(a: List<&2, S.Piece>, b: List<&2, S.Piece>) -> List<&2, S.Piece>:
  List.append(&2, S.Piece, a, b)

def sp_line(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.AtStart{}, ps, True{}}

def sp_starts(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.AtStart{}, ps, False{}}

def sp_holds(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.Anywhere{}, ps, False{}}

def sp_ends(ps: List<&2, S.Piece>) -> S.Shape:
  S.Shape{S.Anywhere{}, ps, True{}}

# R3, R4: a name whose word chars from its start hold a secret word
# (fold: in either case), captured
def sp_secret_name(xs: List<&2, List<&2, S.Piece>>) -> S.Piece:
  S.Cap{[S.Ahead{sp_cat([sp_any(sp_wordc())], sp_one_of(xs)), False{}}, sp_1(sp_lead()), sp_any(sp_wordc())]}

def sp_secrets() -> List<&2, String>:
  ["token", "key", "secret", "password"]

# R43, R44: an assignment
def sp_assign() -> List<&2, S.Piece>:
  [sp_any(sp_blank()), sp_1(sp_lead()), sp_any(sp_wordc()), sp_or_none([sp_any(sp_blank()), sp_t(":"), sp_any(sp_space()), sp_some(sp_not([sp_r(61)]))]), sp_any(sp_blank()), sp_t("="), sp_any(sp_blank()), sp_await()]

# R33, R34: `subprocess.`, the function, `(`, White_Space
def sp_subprocess() -> List<&2, S.Piece>:
  sp_cat([sp_t("subprocess.")], sp_cat(sp_words(["run", "check_call", "check_output", "Popen"]), [sp_t("("), sp_any(sp_space())]))

# R47: tabs and spaces; a CR; a line feed
def sp_tabs() -> S.Piece:
  sp_any(sp_in([sp_r(9), sp_r(32)]))

def sp_cr() -> S.Piece:
  sp_1(sp_in([sp_r(13)]))

def sp_lf() -> S.Piece:
  sp_1(sp_in([sp_r(10)]))

# R1-R47, by id from 130
def sp_table() -> List<&2, S.Shape>:
  [sp_holds([sp_some(sp_blank())]),
   sp_holds([S.Run{sp_in([sp_r(43), sp_r(47), S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]), 80n, None{}}, S.Run{sp_in([sp_r(61)]), 0n, Some{2n}}]),
   sp_holds([S.Bound{}, sp_secret_name(sp_lits(sp_secrets())), sp_any(sp_blank()), sp_t("="), sp_any(sp_blank()), S.Cap{[sp_1(sp_q())]}, sp_any(sp_nq()), S.Same{2n}]),
   sp_holds([S.Bound{}, sp_secret_name(sp_folds(sp_secrets())), sp_any(sp_blank()), sp_t("="), sp_any(sp_blank()), S.Ahead{[S.Fold{"<redacted>"}], True{}}, S.Ahead{[sp_1(sp_q())], True{}}, sp_some(sp_dark())]),
   sp_holds([S.Bound{}, S.Cap{[S.Fold{"authorization:"}, sp_any(sp_space()), sp_or_none([S.Fold{"bearer"}, sp_some(sp_space())])]}, sp_some(sp_not(List.append(&2, S.Rg, sp_white(), [sp_r(34), sp_r(39)])))]),
   sp_holds([S.Cap{[sp_1(sp_q())]}, sp_t("sk-"), sp_some(sp_nq()), S.Same{1n}]),
   sp_holds([S.Cap{[sp_1(sp_q())]}, S.Run{sp_nolf(), 160n, None{}}, S.Same{1n}]),
   sp_starts([sp_any(sp_blank()), sp_t("!")]),
   sp_starts([sp_any(sp_blank()), sp_t("cd"), sp_some(sp_blank()), S.Cap{[sp_some(sp_not([sp_r(38), sp_r(59), sp_r(124)]))]}, S.Alt{[sp_t("&&")], [sp_t(";")]}, sp_any(sp_blank())]),
   sp_starts([sp_any(sp_blank()), sp_t("#")]),
   sp_line([sp_any(sp_blank()), sp_t("set"), sp_some(sp_blank()), sp_1(sp_in([sp_r(43), sp_r(45)])), sp_any(sp_in([S.Rg{65, 90}, S.Rg{97, 122}])), S.Many{[sp_some(sp_blank()), sp_or_none([sp_1(sp_in([sp_r(43), sp_r(45)]))]), sp_some(sp_wordc())], 0n}, sp_or_none([sp_some(sp_blank()), sp_t("pipefail")]), sp_any(sp_blank())]),
   sp_starts(sp_one_of([[sp_t("export"), sp_some(sp_blank()), sp_some(sp_wordc()), sp_t("=")], [sp_t("source"), sp_some(sp_blank()), sp_some(sp_dark())], [sp_t("."), sp_some(sp_blank()), sp_some(sp_dark())]])),
   sp_holds(sp_one_of([[sp_t("\""), S.Cap{[sp_any(sp_not([sp_r(34)]))]}, sp_t("\"")], [sp_t("'"), S.Cap{[sp_any(sp_not([sp_r(39)]))]}, sp_t("'")], [S.Cap{[sp_some(sp_dark())]}]])),
   sp_starts([sp_t("./")]),
   sp_ends([S.Alt{[S.Begin{}], [sp_t("/")]}, sp_t("vitest/dist/cli.js")]),
   sp_holds([sp_any(sp_dark()), sp_t("node_modules/.bin/")]),
   sp_holds([sp_any(sp_space()), S.Alt{[sp_t("&&")], [sp_t(";")]}, sp_any(sp_space())]),
   sp_holds([sp_t("<<"), sp_or_none([sp_t("-")]), sp_any(sp_space()), sp_or_none([sp_1(sp_q())]), S.Cap{sp_name()}, sp_or_none([sp_1(sp_q())])]),
   sp_holds([S.Bound{}, sp_or_none([sp_t("uv"), sp_some(sp_blank()), sp_t("run"), sp_some(sp_blank())]), sp_t("python"), sp_or_none([sp_t("3")]), S.Bound{}]),
   sp_holds([S.Alt{[S.Begin{}], [sp_1(sp_not([sp_r(46), S.Rg{48, 57}, S.Rg{65, 90}, sp_r(95), S.Rg{97, 122}]))]}, S.Alt{[sp_t("bash")], [sp_t("sh")]}, S.Bound{}]),
   sp_holds([S.Bound{}, sp_t("node"), S.Bound{}]),
   sp_holds([S.Bound{}, S.Alt{[sp_t("cat")], [sp_t("tee")]}, S.Bound{}, sp_any(sp_nolf()), S.Alt{[sp_t(">")], [sp_1(sp_space())]}, S.Cap{[sp_some(sp_dark())]}, sp_any(sp_space()), sp_t("<<"), sp_or_none([sp_t("-")])]),
   sp_holds([S.Bound{}, sp_t("apply_patch"), S.Bound{}]),
   sp_holds(sp_cat([S.Bound{}], sp_cat(sp_one_of([[sp_t("rm")], [sp_t("mv")], [sp_t("cp")], [sp_t("git"), sp_some(sp_blank()), S.Alt{[sp_t("add")], [sp_t("commit")]}], [sp_t("npm"), sp_some(sp_blank()), sp_t("install")], [sp_t("sed"), sp_some(sp_blank()), sp_t("-i")], [sp_t("perl"), sp_some(sp_blank()), sp_t("-pi")], [sp_t("tee")], [sp_t("cat"), sp_any(sp_blank()), sp_t(">")], [sp_t("apply_patch")]]), [S.Bound{}]))),
   sp_starts([sp_any(sp_blank()), S.Alt{[sp_t("import"), sp_some(sp_blank()), sp_1(sp_dark())], [sp_t("from"), sp_some(sp_blank()), sp_some(sp_dark()), sp_some(sp_blank()), sp_t("import"), sp_some(sp_blank())]}]),
   sp_starts([sp_any(sp_blank())]),
   sp_starts([sp_any(sp_blank()), sp_await(), sp_1(sp_lead()), sp_any(sp_dotted()), sp_any(sp_blank()), sp_t("(")]),
   sp_starts(sp_cat([sp_any(sp_blank()), sp_await()], sp_cat(sp_words(["print", "len", "str", "repr", "int", "float", "list", "dict", "set", "tuple"]), [sp_any(sp_blank()), sp_t("(")]))),
   sp_line([sp_t("print("), S.Cap{[sp_any(sp_nolf())]}, sp_t(")")]),
   sp_starts([sp_any(sp_blank()), S.Cap{sp_name()}, sp_any(sp_blank()), sp_t("="), sp_any(sp_blank()), S.Alt{[sp_t("Path")], [sp_t("pathlib.Path")]}, sp_t("("), S.Cap{[sp_1(sp_q())]}, S.Cap{[sp_some(sp_nq())]}, S.Same{2n}, sp_t(")")]),
   sp_starts([sp_any(sp_blank()), S.Cap{sp_name()}, sp_any(sp_blank()), sp_t("="), sp_any(sp_blank()), S.Cap{[sp_1(sp_q())]}, S.Cap{[sp_some(sp_nq())]}, S.Same{2n}]),
   sp_starts([sp_or_none([sp_t("await"), sp_some(sp_space())]), S.Cap{sp_name()}, sp_t("."), S.Cap{sp_words(["write_text", "write_bytes", "read_text", "read_bytes", "mkdir", "unlink", "rename", "replace", "touch"])}, sp_any(sp_space()), sp_t("(")]),
   sp_holds(sp_cat(sp_subprocess(), [S.Cap{[sp_1(sp_in([sp_r(34), sp_r(96)]))]}, S.Cap{[sp_some(sp_not([sp_r(34), sp_r(96)]))]}, S.Same{1n}])),
   sp_holds(sp_cat(sp_subprocess(), [sp_t("["), S.Cap{[sp_some(sp_not([sp_r(93)]))]}, sp_t("]")])),
   sp_holds([sp_1(sp_q()), S.Cap{[sp_some(sp_nq())]}, sp_1(sp_q())]),
   sp_starts(sp_cat([sp_any(sp_blank())], sp_cat(sp_one_of([[sp_t("async"), sp_some(sp_blank()), sp_t("def")], [sp_t("def")], [sp_t("class")]]), [sp_some(sp_blank())]))),
   sp_starts([sp_any(sp_blank()), sp_t("@")]),
   sp_line(sp_cat([sp_any(sp_blank())], sp_cat(sp_words(["if", "elif", "else", "for", "while", "with", "try", "except", "finally"]), [S.Bound{}, sp_any(sp_nolf()), sp_t(":"), sp_any(sp_space())]))),
   sp_ends([sp_t(":"), sp_any(sp_space())]),
   sp_line([sp_some(sp_in(List.append(&2, S.Rg, sp_white(), [sp_r(41), sp_r(44), sp_r(59), sp_r(93), sp_r(125)]))), sp_or_none([sp_t("#"), sp_any(sp_nolf())])]),
   sp_starts([sp_any(sp_blank()), sp_t("if"), sp_some(sp_blank()), sp_t("__name__"), sp_any(sp_blank()), sp_t("=="), sp_any(sp_blank()), sp_1(sp_q()), sp_t("__main__"), sp_1(sp_q()), sp_any(sp_blank()), sp_t(":")]),
   sp_starts(sp_cat([sp_any(sp_blank()), sp_await(), sp_1(sp_lead()), sp_any(sp_dotted()), sp_t(".")], sp_cat(sp_words(["write_text", "write_bytes", "mkdir", "unlink", "rename", "replace", "touch", "append", "extend", "update", "add", "remove", "discard", "close", "commit", "execute", "run"]), [sp_any(sp_blank()), sp_t("(")]))),
   sp_starts(sp_cat(sp_assign(), sp_cat(sp_words(["Path", "pathlib.Path", "json.loads", "json.dumps", "str", "int", "float", "list", "dict", "set", "tuple"]), [sp_any(sp_blank()), sp_t("(")]))),
   sp_starts(sp_cat(sp_assign(), [sp_1(sp_lead()), sp_any(sp_dotted()), sp_any(sp_blank()), sp_t("(")])),
   sp_holds([sp_any(sp_blank()), sp_or_none([sp_1(sp_lead()), sp_any(sp_wordc()), sp_any(sp_blank()), sp_t("="), sp_any(sp_blank())]), sp_await(), sp_t("bash"), sp_any(sp_blank()), sp_t("("), sp_any(sp_blank()), sp_or_none([sp_1(sp_in([sp_r(82), sp_r(114)]))]), S.Cap{sp_words(["\"\"\"", "'''", "\"", "'"])}]),
   sp_starts([S.Cap{[sp_any(sp_blank())]}, sp_t(";"), sp_any(sp_blank())]),
   sp_starts([S.Many{[sp_tabs(), sp_or_none([sp_cr()]), sp_lf()], 0n}, sp_tabs(), sp_t("%%bash"), S.Bound{}, sp_any(sp_not([sp_r(10), sp_r(13)])), sp_or_none([sp_or_none([sp_cr()]), sp_lf()])])]

# Laws
# ----

# LAW preview_shapes_table (R1-R48): at every index the table holds the
# shape R1-R47 state for its id, and none past them
# EXCLUDES: a shape that drifts from the regex it replaced (a piece lost,
#   added or reordered, a capture moved, another class, a shape read
#   anywhere that must start the line, a missing end), ids shifted, a
#   lookup that answers a shape past the last
law preview_shapes_table:
  for +i: Nat
  {PS.shape(i) == List.get(&2, S.Shape, sp_table(), i) : Maybe<&2, S.Shape>}

# LAW preview_shapes_redact_example (R2, R3): anchor: the redaction test's
# 80-digit blob is a blob, and its token assignment a quoted secret whose
# name and quote are captured
# EXCLUDES: a table that drifts from the preview's tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   preview_shapes_table pins it whole to its R rule
law preview_shapes_redact_example:
  {[S.first([PS.blob()], "01234567890123456789012345678901234567890123456789012345678901234567890123456789"), S.first([PS.secret_quoted()], "api_token = \"abc123\" and")] == [Some{S.Found{0n, S.Fit{0n, 80n, []}}}, Some{S.Found{0n, S.Fit{0n, 20n, [Some{"api_token"}, Some{"\""}]}}}] : List<&2, Maybe<&2, S.Found>>}

# LAW preview_shapes_chain_example (R13, R17, R24): anchor: the chain test's
# command splits at its two `&&`, its middle part is a mutation, and the
# npm test's command reads as its five words (each the third capture)
# EXCLUDES: a table that drifts from the preview's tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   preview_shapes_table pins it whole to its R rule
law preview_shapes_chain_example:
  {(S.all(PS.chain_sep(), "echo start && git commit -m x && ls"), (S.first([PS.mutation()], "git commit -m x"), S.all(PS.shell_word(), "npm run test -- --watch"))) == ([S.Fit{10n, 14n, []}, S.Fit{29n, 33n, []}], (Some{S.Found{0n, S.Fit{0n, 10n, []}}}, [S.Fit{0n, 3n, [None{}, None{}, Some{"npm"}]}, S.Fit{4n, 7n, [None{}, None{}, Some{"run"}]}, S.Fit{8n, 12n, [None{}, None{}, Some{"test"}]}, S.Fit{13n, 15n, [None{}, None{}, Some{"--"}]}, S.Fit{16n, 23n, [None{}, None{}, Some{"--watch"}]}])) : List<&2, S.Fit> & (Maybe<&2, S.Found> & List<&2, S.Fit>)}

# LAW preview_shapes_heredoc_example (R18, R19): anchor: the python heredoc
# test's opener gives its delimiter and runs python
# EXCLUDES: a table that drifts from the preview's tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   preview_shapes_table pins it whole to its R rule
law preview_shapes_heredoc_example:
  {[S.first([PS.heredoc()], "python3 <<'EOF'"), S.first([PS.python_run()], "python3 <<'EOF'")] == [Some{S.Found{0n, S.Fit{8n, 15n, [Some{"EOF"}]}}}, Some{S.Found{0n, S.Fit{0n, 7n, []}}}] : List<&2, Maybe<&2, S.Found>>}

# LAW preview_shapes_python_example (R30, R32, R45): anchor: the python
# tests' path assignment (the first of the two assignment shapes), file
# write and bash skill call, with their captures
# EXCLUDES: a table that drifts from the preview's tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   preview_shapes_table pins it whole to its R rule
law preview_shapes_python_example:
  {[S.first([PS.path_assign(), PS.string_assign()], "p = Path('src/a.ts')"), S.first([PS.file_op()], "p.write_text('data')"), S.first([PS.bash_call()], "await bash(\"git status --porcelain\")")] == [Some{S.Found{0n, S.Fit{0n, 20n, [Some{"p"}, Some{"'"}, Some{"src/a.ts"}]}}}, Some{S.Found{0n, S.Fit{0n, 13n, [Some{"p"}, Some{"write_text"}]}}}, Some{S.Found{0n, S.Fit{0n, 12n, [Some{"\""}]}}}] : List<&2, Maybe<&2, S.Found>>}

# LAW preview_shapes_cell_example (R47): anchor: the cell tests' magic
# lines, alone and after blank lines, end where the body starts; a longer
# word or a quoted magic is none
# EXCLUDES: a table that drifts from the cell tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   preview_shapes_table pins it whole to its R rule
law preview_shapes_cell_example:
  {[S.first([PS.bash_magic()], "%%bash\necho hi"), S.first([PS.bash_magic()], "\n\t\n  %%bash -l\nls"), S.first([PS.bash_magic()], "  %%bashish\n"), S.first([PS.bash_magic()], "x = '%%bash'")] == [Some{S.Found{0n, S.Fit{0n, 7n, []}}}, Some{S.Found{0n, S.Fit{0n, 15n, []}}}, None{}, None{}] : List<&2, Maybe<&2, S.Found>>}

# eukhe: the laws of area autolink_shapes

import Base
import ../bend/shape.bend as S
import ../bend/autolink_shapes.bend as AL

# (AL1) The shapes of marked's GFM autolink rules
# -----------------------------------------------
# bend/autolink_shapes.bend, ids 120-129 of the entry bend/ffi_shape.bend
# (eukhe-tui autolink.rs asks them through eukhe-tui text_shapes.rs, in
# place of marked 18.0.7's `autolink`, gfm `url` and `_backpedal` regexes).
# The matcher is pinned by laws/shape/match.bend and
# laws/shape/search.bend. "White_Space" is Unicode White_Space (9-13,
# space, U+0085, U+00A0, U+1680, U+2000-U+200A, U+2028, U+2029, U+202F,
# U+205F, U+3000); "a letter or digit" A-Z, a-z, 0-9; "a label char" a
# letter, digit or `-`. "the text starts with" a shape read at the text
# start; "the text holds" one read at the leftmost place it fits. A class
# lists its White_Space ranges first, then its other codes, each from the
# lowest up.
#
# R1: id 120, an angle link: the text starts with `<`, then (captured: the
#     target) either an ASCII letter, 1 to 31 chars each a letter, digit,
#     `+`, `-` or `.`, `:`, then chars none of White_Space, codes 0-32, `<`
#     and `>` (none too); or else one or more chars each a letter, digit or
#     one of ``!#$%&'*+-./=?^_`{|}~``, `@` (captured), a letter or digit,
#     then up to 61 label chars and a letter or digit, or nothing; then one
#     or more rounds of `.`, a letter or digit, then up to 61 label chars
#     and a letter or digit, or nothing; where no `-` or `_` comes next;
#     then `>`.
# R2: id 121, a bare link: the text starts with either (captured: the
#     scheme) `http` and `s` or nothing, or `ftp`, each in either case of
#     ASCII letters, then `://`; or else `www.`; then a label char, then
#     chars none of White_Space and `<` (none too) (marked's
#     `(?:[a-zA-Z0-9\-]+\.?)+` before `[^\s<]*` reads only chars the latter
#     takes, so it adds nothing past its first char); or else one or more
#     chars each a letter, digit, `+`, `-`, `.` or `_`, `@` (captured), one
#     or more chars each a label char or `_`, one or more rounds of `.`,
#     label chars and `_` (none too) and a letter or digit; where no `-` or
#     `_` comes next.
# R3: id 122, the backpedal: the text holds one or more rounds, each chosen
#     by its first char: a whole run of chars none of ``?!.,:;*_'"~()&``
#     (no such char comes next); or `(`, chars that are no `)` (none too),
#     `)`; or `&` where one or more letters and digits, `;` and the text end
#     do not come next; or a whole run of punctuation chars
#     (``?!.,:;*_'"~)``) where no punctuation and not the text end comes
#     next; or such a run but its last char, where that last char ends the
#     text (marked's rounds take each run whole, or before `(?!$)` all but
#     its last char, and nothing after the rounds makes them go back).
# R4: the table holds exactly these shapes, the one of id 120 + i at index
#     i, and no other.
#
# Anchored only: R1-R3 (autolink_shapes_link_example,
# autolink_shapes_backpedal_example, autolink_shapes_fixture_example). No
# source outside eukhe's code holds marked 18.0.7's regexes, so a law over
# the table would compare it with itself; a law by meaning over every text
# needs the matcher's search (bend/shape.bend) reasoned through for these
# shapes, not done. The requirement's marked fixtures are the outside table
# the anchors follow. R4 (ids, none past the last) is stated for the entry by
# laws/shape/entry.bend (area shape), which reads sp_table.

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

def sp_some(c: S.Cls) -> S.Piece:
  S.Run{c, 1n, None{}}

def sp_any(c: S.Cls) -> S.Piece:
  S.Run{c, 0n, None{}}

def sp_alnum() -> S.Cls:
  sp_in([S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}])

def sp_label() -> S.Cls:
  sp_in([sp_r(45), S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}])

def sp_label_() -> S.Cls:
  sp_in([sp_r(45), S.Rg{48, 57}, S.Rg{65, 90}, sp_r(95), S.Rg{97, 122}])

# where no `-` or `_` comes next
def sp_no_dash() -> S.Piece:
  S.Ahead{[sp_1(sp_in([sp_r(45), sp_r(95)]))], True{}}

# up to 61 label chars and a letter or digit, or nothing
def sp_tail() -> S.Piece:
  S.Opt{[S.Run{sp_label(), 0n, Some{61n}}, sp_1(sp_alnum())]}

# R3: none of ``?!.,:;*_'"~()&``; the punctuation ``?!.,:;*_'"~)``
def sp_plain() -> S.Cls:
  sp_not([sp_r(33), sp_r(34), sp_r(38), sp_r(39), sp_r(40), sp_r(41), sp_r(42), sp_r(44), sp_r(46), sp_r(58), sp_r(59), sp_r(63), sp_r(95), sp_r(126)])

def sp_punct() -> S.Cls:
  sp_in([sp_r(33), sp_r(34), sp_r(39), sp_r(41), sp_r(42), sp_r(44), sp_r(46), sp_r(58), sp_r(59), sp_r(63), sp_r(95), sp_r(126)])

# R1-R3, by id from 120: the shapes written out, read by
# laws/shape/entry.bend (sp_shape_of, area shape) for ids 120-129; no law
# of this area uses it
def sp_table() -> List<&2, S.Shape>:
  [S.Shape{S.AtStart{}, [S.Lit{"<"}, S.Cap{[S.Alt{[sp_1(sp_in([S.Rg{65, 90}, S.Rg{97, 122}])), S.Run{sp_in([sp_r(43), S.Rg{45, 46}, S.Rg{48, 57}, S.Rg{65, 90}, S.Rg{97, 122}]), 1n, Some{31n}}, S.Lit{":"}, sp_any(sp_not(List.append(&2, S.Rg, sp_white(), [S.Rg{0, 32}, sp_r(60), sp_r(62)])))], [sp_some(sp_in([sp_r(33), S.Rg{35, 39}, S.Rg{42, 43}, S.Rg{45, 57}, sp_r(61), sp_r(63), S.Rg{65, 90}, S.Rg{94, 126}])), S.Cap{[S.Lit{"@"}]}, sp_1(sp_alnum()), sp_tail(), S.Many{[S.Lit{"."}, sp_1(sp_alnum()), sp_tail()], 1n}, sp_no_dash()]}]}, S.Lit{">"}], False{}},
   S.Shape{S.AtStart{}, [S.Alt{[S.Cap{[S.Alt{[S.Alt{[S.Fold{"http"}, S.Opt{[S.Fold{"s"}]}], [S.Fold{"ftp"}]}, S.Lit{"://"}], [S.Lit{"www."}]}]}, sp_1(sp_label()), sp_any(sp_not(List.append(&2, S.Rg, sp_white(), [sp_r(60)])))], [sp_some(sp_in([sp_r(43), S.Rg{45, 46}, S.Rg{48, 57}, S.Rg{65, 90}, sp_r(95), S.Rg{97, 122}])), S.Cap{[S.Lit{"@"}]}, sp_some(sp_label_()), S.Many{[S.Lit{"."}, sp_any(sp_label_()), sp_1(sp_alnum())], 1n}, sp_no_dash()]}], False{}},
   S.Shape{S.Anywhere{}, [S.Many{[S.Alt{[sp_some(sp_plain()), S.Ahead{[sp_1(sp_plain())], True{}}], [S.Alt{[S.Lit{"("}, sp_any(sp_not([sp_r(41)])), S.Lit{")"}], [S.Alt{[S.Lit{"&"}, S.Ahead{[sp_some(sp_alnum()), S.Lit{";"}, S.End{}], True{}}], [S.Alt{[sp_some(sp_punct()), S.Ahead{[sp_1(sp_punct())], True{}}, S.Ahead{[S.End{}], True{}}], [sp_some(sp_punct()), S.Ahead{[sp_1(sp_punct()), S.End{}], False{}}]}]}]}]}], 1n}], False{}}]

# Laws
# ----

# LAW autolink_shapes_link_example (R1, R2): anchor: the renderer tests'
# angle url and angle email (the `@` captured), a bare url read up to the
# space (its trailing `.` still in), a bare email and a `www.` link
# EXCLUDES: a link shape that drifts from the renderer tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   no source outside eukhe states the shapes (see R1-R3 above)
law autolink_shapes_link_example:
  {[S.first([AL.angle()], "<https://angle.dev/a> y"), S.first([AL.angle()], "<foo.bar@example.org>"), S.first([AL.bare()], "https://x.dev/pull/182. now"), S.first([AL.bare()], "foo.bar+baz@example.com ok"), S.first([AL.bare()], "www.example.com/path")] == [Some{S.Found{0n, S.Fit{0n, 21n, [Some{"https://angle.dev/a"}, None{}]}}}, Some{S.Found{0n, S.Fit{0n, 21n, [Some{"foo.bar@example.org"}, Some{"@"}]}}}, Some{S.Found{0n, S.Fit{0n, 23n, [Some{"https://"}, None{}]}}}, Some{S.Found{0n, S.Fit{0n, 23n, [None{}, Some{"@"}]}}}, Some{S.Found{0n, S.Fit{0n, 20n, [Some{"www."}, None{}]}}}] : List<&2, Maybe<&2, S.Found>>}

# LAW autolink_shapes_backpedal_example (R3): anchor: the renderer tests'
# trailing punctuation: a final `.` and `,` are left out, a balanced paren
# group is kept and a lone final `)` left out
# EXCLUDES: a backpedal that drifts from the renderer tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   no source outside eukhe states the shapes (see R1-R3 above)
law autolink_shapes_backpedal_example:
  {[S.first([AL.backpedal()], "https://x.dev/pull/182."), S.first([AL.backpedal()], "https://x.dev/a(b))"), S.first([AL.backpedal()], "https://x.dev/page,")] == [Some{S.Found{0n, S.Fit{0n, 22n, []}}}, Some{S.Found{0n, S.Fit{0n, 18n, []}}}, Some{S.Found{0n, S.Fit{0n, 18n, []}}}] : List<&2, Maybe<&2, S.Found>>}

# LAW autolink_shapes_fixture_example (R1-R3): anchor: the requirement's
# marked fixture `autolinks`: its source `<https://x.test/a> <me@example.com>
# www.example.com https://example.com/a_(b).` lexes to an angle url link
# `<https://x.test/a>`, an angle email link `<me@example.com>`, a `www.`
# link `www.example.com` (ended by the space) and a url link
# `https://example.com/a_(b)`, the final `.` text: the angle shape reads
# each angle link whole from its `<` (target captured, the `@` too), the
# bare shape reads the `www.` link to the space and the url to the end,
# and the backpedal leaves the final `.` out and keeps `_` and `(b)`
# EXCLUDES: a link shape that drifts from the fixture (a `_` or a paren
# group cut, the final `.` kept, an angle link cut at its `@`)
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   no source outside eukhe states the shapes (see R1-R3 above)
law autolink_shapes_fixture_example:
  {[S.first([AL.angle()], "<https://x.test/a> <me@example.com> www.example.com https://example.com/a_(b)."), S.first([AL.angle()], "<me@example.com> www.example.com https://example.com/a_(b)."), S.first([AL.bare()], "www.example.com https://example.com/a_(b)."), S.first([AL.bare()], "https://example.com/a_(b)."), S.first([AL.backpedal()], "https://example.com/a_(b).")] == [Some{S.Found{0n, S.Fit{0n, 18n, [Some{"https://x.test/a"}, None{}]}}}, Some{S.Found{0n, S.Fit{0n, 16n, [Some{"me@example.com"}, Some{"@"}]}}}, Some{S.Found{0n, S.Fit{0n, 15n, [Some{"www."}, None{}]}}}, Some{S.Found{0n, S.Fit{0n, 26n, [Some{"https://"}, None{}]}}}, Some{S.Found{0n, S.Fit{0n, 25n, []}}}] : List<&2, Maybe<&2, S.Found>>}

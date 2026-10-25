# codemode_id: the identifier a code-mode script uses for a tool (port of
# pi-codemode `identifier.ts`; the Rust host is
# crates/eukhe-durable/src/codemode/identifier.rs). Each char of the tool's
# name that a JavaScript identifier may not hold at its place becomes `_`:
# the first char may be an ASCII letter, `_` or `$`; a later char also an
# ASCII digit. Chars are code points (JS `for...of`), so a char past ASCII
# becomes one `_`. An empty name is `_`. `mcp__docs__search` stays as is,
# `my-tool` is `my_tool`, `1st.tool` is `_st_tool`. Pure: no IO, no
# @unsafe. laws/codemode_id.bend states its laws.
#
# `test` answers whether a text is already such an identifier (a global's
# name, an object key written bare): the same classes.

import Base

# Classes
# -------

# x is the code of an ASCII letter
def letter(+x: U32) -> Bool:
  Bool.or(Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), Bool.and(U32.is_le(97, x), U32.is_le(x, 122)))

# x is the code of `_` or `$`
def mark(+x: U32) -> Bool:
  Bool.or(U32.is_eq(x, 95), U32.is_eq(x, 36))

# x is the code of an ASCII digit
def digit(+x: U32) -> Bool:
  Bool.and(U32.is_le(48, x), U32.is_le(x, 57))

# c may start an identifier: an ASCII letter, `_` or `$`
def start(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(letter(x), mark(x))

# c may continue an identifier: what may start one, or an ASCII digit
def part(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.or(letter(x), mark(x)), digit(x))

# The identifier
# --------------

# c where it may stand, else `_`
def keep(ok: Bool, c: Char) -> Char:
  match ok:
    case True{}:
      c
    case False{}:
      '_'

# the chars after the first
def rest(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      SCon{keep(part(c), c), rest(t)}

# the identifier of the tool named s
def of(s: String) -> String:
  match s:
    case SNil{}:
      "_"
    case SCon{+c, t}:
      SCon{keep(start(c), c), rest(t)}

# The identifier test
# -------------------

# every char of s may continue an identifier
def parts(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(part(c), parts(t))

# s is an identifier: not empty, its first char may start one, every later
# char may continue one
def test(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.and(start(c), parts(t))

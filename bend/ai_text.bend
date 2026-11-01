# ai_text: texts the eukhe-ai providers read (api/google_shared.rs,
# api/google_vertex.rs, api/openrouter_images.rs, api/mistral_conversations,
# utils): a Gemini id's major version, an API version in a URL path, a
# base64 data URL, and the event boundaries and lines of a server-sent event
# stream. Each is a plain string rule (a prefix taken off, a run of digits
# read, one pass over the text); laws/ai_text.bend states each in plain
# words over splits of the text. Above each rule: the regex it replaced. A
# digit here is 0-9 (Rust's `\d` takes every Unicode digit: an intended
# difference). Pure: no IO, no @unsafe.

import Base
import ./text_pat.bend as Tp
import ./phrase.bend as P
import ./model_name.bend as M

# Runs of digits
# --------------

def dig.take.at(b: Bool, x: Char, rest: Unit -> String) -> String:
  match b:
    case True{}:
      SCon{x, rest(Unit{})}
    case False{}:
      SNil{}

# the digits at the start of s
def dig.take(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+x, +t}:
      dig.take.at(Tp.is_dig(x), x, u => dig.take(t))

def dig.drop.at(b: Bool, s: String, rest: Unit -> String) -> String:
  match b:
    case True{}:
      rest(Unit{})
    case False{}:
      s

# s after the digits at its start
def dig.drop(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+x, +t}:
      dig.drop.at(Tp.is_dig(x), SCon{x, t}, u => dig.drop(t))

def found(b: Bool, r: String) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{r}
    case False{}:
      None{}

# R1: a Gemini id's major version
# -------------------------------

# the digits at the start of s, when there are some
def major.digits(+s: String) -> Maybe<&2, String>:
  found(Bool.not(String.is_empty(dig.take(s))), dig.take(s))

def major.live(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      major.digits(r)

def major.or(m: Maybe<&2, String>, rest: Unit -> Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      rest(Unit{})
    case Some{x}:
      Some{x}

def major.after(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+r}:
      major.or(major.digits(r), u => major.live(M.strip("live-", r)))

# ^gemini(?:-live)?-(\d+)
def gemini_major(id: String) -> Maybe<&2, String>:
  major.after(M.strip("gemini-", id))

# R2: an API version in a path
# ----------------------------

# s ends here or a `/` follows
def at_end(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Char.is_eq(x, '/')

def ver.beta(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      at_end(dig.drop(r))

# after the digits: the end of the part, or `beta`, digits, the end
def ver.tail(+s: String) -> Bool:
  P.pm.or(at_end(s), u => ver.beta(M.strip("beta", s)))

def ver.at(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+r}:
      P.pm.and(Bool.not(String.is_empty(dig.take(r))), u => ver.tail(dig.drop(r)))

# whether the part of s up to its first `/` is an API version:
# ^v\d+(?:beta\d*)?$
def ver(+s: String) -> Bool:
  ver.at(M.strip("v", s))

# whether a part of s that starts here (start: at the text's start or
# after a `/`) or later is an API version
def api.go(s: String, start: Bool) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+x, +t}:
      P.pm.or(P.pm.and(start, u => ver(SCon{x, t})), v => api.go(t, Char.is_eq(x, '/')))

# (?:^|/)v\d+(?:beta\d*)?(?:/|$)
def api_version(s: String) -> Bool:
  api.go(s, True{})

# R3: a base64 data URL
# ---------------------

# where the reading is: in `data:` (the chars left), in the mime (its
# length so far), in `;base64,` past the `;` (the chars left), in the data
# (any: a data char was read), or failed
type Du is Data:
  DPre{left: String}
  DMime{n: Nat}
  DMark{n: Nat, left: String}
  DData{n: Nat, any: Bool}
  DFail{}

# a line terminator: U+000A, U+000D, U+2028, U+2029
def is_lt(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(U32.is_eq(x, 10), Bool.or(U32.is_eq(x, 13), Bool.or(U32.is_eq(x, 8232), U32.is_eq(x, 8233))))

def du.pre(ok: Bool, lt: String) -> Du:
  match ok:
    case True{}:
      match lt:
        case SNil{}:
          DMime{0n}
        case SCon{y, u}:
          DPre{SCon{y, u}}
    case False{}:
      DFail{}

def du.mark(ok: Bool, +n: Nat, lt: String) -> Du:
  match ok:
    case True{}:
      match lt:
        case SNil{}:
          DData{n, False{}}
        case SCon{y, u}:
          DMark{n, SCon{y, u}}
    case False{}:
      DFail{}

def du.mime(semi: Bool, n: Nat) -> Du:
  match semi:
    case True{}:
      match n:
        case 0n:
          DFail{}
        case 1n+k:
          DMark{1n+k, "base64,"}
    case False{}:
      DMime{1n+n}

def du.data(bad: Bool, n: Nat) -> Du:
  match bad:
    case True{}:
      DFail{}
    case False{}:
      DData{n, True{}}

def du.step(st: Du, +c: Char) -> Du:
  match st:
    case DPre{l}:
      match l:
        case SNil{}:
          DFail{}
        case SCon{y, lt}:
          du.pre(Char.is_eq(y, c), lt)
    case DMime{n}:
      du.mime(Char.is_eq(c, ';'), n)
    case DMark{n, l}:
      match l:
        case SNil{}:
          DFail{}
        case SCon{y, lt}:
          du.mark(Char.is_eq(y, c), n, lt)
    case DData{n, any}:
      du.data(is_lt(c), n)
    case DFail{}:
      DFail{}

# the state after s, from st (one pass)
def du.go(s: String, st: Du) -> Du:
  match s:
    case SNil{}:
      st
    case SCon{+c, t}:
      du.go(t, du.step(st, c))

# the state after the chunks, in order (one pass over each)
def du.chunks(cs: List<&2, String>, st: Du) -> Du:
  match cs:
    case Nil{}:
      st
    case c <> more:
      du.chunks(more, du.go(c, st))

def du.verdict.d(any: Bool, n: Nat) -> Maybe<&2, Nat>:
  match any:
    case True{}:
      Some{n}
    case False{}:
      None{}

def du.verdict(st: Du) -> Maybe<&2, Nat>:
  match st:
    case DPre{l}:
      None{}
    case DMime{n}:
      None{}
    case DMark{n, l}:
      None{}
    case DData{n, any}:
      du.verdict.d(any, n)
    case DFail{}:
      None{}

# ^data:([^;]+);base64,([^\n\r\u{2028}\u{2029}]+)$ over the chunks read as
# one text: the length of the mime in chars
def data_url(cs: List<&2, String>) -> Maybe<&2, Nat>:
  du.verdict(du.chunks(cs, DPre{"data:"}))

# R4: the event boundary
# ----------------------

def is_cr(c: Char) -> Bool:
  Char.is_eq(c, '\r')

def is_lf(c: Char) -> Bool:
  Char.is_eq(c, '\n')

def brk.lf(lf: Bool) -> Nat:
  match lf:
    case True{}:
      2n
    case False{}:
      1n

# after a `\r`: a `\n` makes the break `\r\n`
def brk.cr(t: String) -> Nat:
  match t:
    case SNil{}:
      1n
    case SCon{y, u}:
      brk.lf(is_lf(y))

def brk.at(cr: Bool, lf: Bool, t: String) -> Nat:
  match cr:
    case True{}:
      brk.cr(t)
    case False{}:
      match lf:
        case True{}:
          1n
        case False{}:
          0n

# the length of the line break at the start of s: `\r\n` 2, else `\r` or
# `\n` 1, none 0
def brk(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{+x, t}:
      brk.at(is_cr(x), is_lf(x), t)

def bnd.second(k: Nat, n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+j:
      Nat.add(k, 1n+j)

def bnd.cr.at(lf: Bool, t: String, u: String) -> Nat:
  match lf:
    case True{}:
      bnd.second(2n, brk(u))
    case False{}:
      bnd.second(1n, brk(t))

# after a `\r`: the first break is `\r\n` when a `\n` follows, else `\r`
def bnd.cr(t: String) -> Nat:
  match t:
    case SNil{}:
      0n
    case SCon{+y, +u}:
      bnd.cr.at(is_lf(y), SCon{y, u}, u)

def bnd.at(cr: Bool, lf: Bool, t: String) -> Nat:
  match cr:
    case True{}:
      bnd.cr(t)
    case False{}:
      match lf:
        case True{}:
          bnd.second(1n, brk(t))
        case False{}:
          0n

# the length of the boundary at the start of s (a line break right after
# another, 2 to 4 chars), 0 when none starts there
def bnd(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{+x, t}:
      bnd.at(is_cr(x), is_lf(x), t)

# where a boundary starts (chars before it) and how long it is
type Span is Data:
  Span{start: Nat, len: Nat}

def shift(m: Maybe<&2, Span>) -> Maybe<&2, Span>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match p:
        case Span{i, l}:
          Some{Span{1n+i, l}}

def boundary.at(b: Nat, rest: Unit -> Maybe<&2, Span>) -> Maybe<&2, Span>:
  match b:
    case 0n:
      shift(rest(Unit{}))
    case 1n+j:
      Some{Span{0n, 1n+j}}

# \r\n\r\n|\r\n\r|\r\n\n|\r\r\n|\n\r\n|\r\r|\n\r|\n\n (leftmost-first): the
# first place where a boundary starts: its start and length, in chars
def event_boundary(s: String) -> Maybe<&2, Span>:
  match s:
    case SNil{}:
      None{}
    case SCon{+x, +t}:
      boundary.at(bnd(SCon{x, t}), u => event_boundary(t))

# R5: lines
# ---------

# c before the first part
def push(c: Char, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      [SCon{c, SNil{}}]
    case p <> more:
      SCon{c, p} <> more

def lines.at(skip: Bool, brk: Bool, cr: Bool, x: Char, rest: Bool -> List<&2, String>) -> List<&2, String>:
  match skip:
    case True{}:
      rest(False{})
    case False{}:
      match brk:
        case True{}:
          "" <> rest(cr)
        case False{}:
          push(x, rest(False{}))

# s split at each line break (cr: the char before s was `\r`, so a `\n`
# here ends that break)
def lines.go(s: String, cr: Bool) -> List<&2, String>:
  match s:
    case SNil{}:
      [""]
    case SCon{+x, t}:
      lines.at(Bool.and(cr, is_lf(x)), Bool.or(is_cr(x), is_lf(x)), is_cr(x), x, c => lines.go(t, c))

# Regex::new(r"\r\n|\r|\n").split(raw)
def lines(s: String) -> List<&2, String>:
  lines.go(s, False{})

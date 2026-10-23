# eukhe: the laws of area theme

import Base
import ../bend/color.bend as Co
import ../bend/theme.bend as T
import ../bend/tui_color.bend as TC

# ---- themes ----

# LAWS (T1): themes. Each law is an open claim about the models in
# bend/theme.bend and bend/color.bend; PROOF.bend proves them (as
# Laws.<law>) with the lemmas of PROOF.bend section themes.

# (T1) Themes
# -----------
# docs/interface.md "Themes", the model in bend/theme.bend: the one theme
# validator and name resolver of crates/eukhe-theme, which the terminal UI
# and the HTML export share. Every input is free: any registered, builtin
# and custom candidates in any order, valid or not; any name; any theme
# file (any colors, variables and export page). The shipped themes are
# the tables of bend/theme.bend; the bridge test
# crates/eukhe-core/src/export_html/theme_bridge.rs checks that they equal
# crates/eukhe-theme/themes/*.json and that the Rust code and the model
# agree on generated files, names and colors.

# LAW: the empty name resolves to the default theme, with no warning
law theme_resolve_empty:
  for src: List<&2, T.Cand>
  {T.resolve.name(src, "") == T.Res{T.dflt(), False{}} : T.Res}

# LAW: a name resolves to the first valid theme that advertises it, with
# no warning: a registered file before a builtin before a custom file
law theme_resolve_first:
  for +pre: List<&2, T.Cand>
  for +nm: String
  for +id: U32
  for +post: List<&2, T.Cand>
  for +n: String
  for ne: {String.is_empty(n) == False{} : Bool}
  for miss: {T.hit(pre, n) == False{} : Bool}
  for same: {String.eq(nm, n) == True{} : Bool}
  {T.resolve.name(List.append(&2, T.Cand, pre, T.Cand{nm, True{}, id} <> post), n) == T.Res{id, False{}} : T.Res}

# LAW: a name that no valid theme advertises (missing, or only in invalid
# files) resolves to the default theme, with a warning: resolution never
# fails
law theme_resolve_missing:
  for +src: List<&2, T.Cand>
  for +n: String
  for ne: {String.is_empty(n) == False{} : Bool}
  for miss: {T.hit(src, n) == False{} : Bool}
  {T.resolve.name(src, n) == T.Res{T.dflt(), True{}} : T.Res}

# LAW: a theme file loads only when it is valid (every color resolves and
# every required token is written)
law theme_load_valid:
  for r: T.RFile
  for -f: T.Th
  for loaded: {T.load(r) == Some{f} : Maybe<&2, T.Th>}
  {T.valid(f) == True{} : Bool}

# LAW: the palette of a valid theme file defines every token
law theme_tokens_complete:
  for f: T.Th
  for v: {T.valid(f) == True{} : Bool}
  {T.complete(T.palette(f)) == True{} : Bool}

# LAW: two theme files with the same background have the same mode, light
# or dark
law theme_mode_background:
  for f: T.Th
  for g: T.Th
  for same: {T.bg(f) == T.bg(g) : Co.Rgb}
  {T.light(f) == T.light(g) : Bool}

# LAW: the name of a theme file never changes its palette
law theme_palette_name_free:
  for f: T.Th
  for n: String
  {T.palette(T.rename(f, n)) == T.palette(f) : List<&2, Maybe<&2, T.Val>>}

# LAW: the name of a theme file never changes its mode
law theme_mode_name_free:
  for f: T.Th
  for n: String
  {T.light(T.rename(f, n)) == T.light(f) : Bool}

# LAW: in every shipped theme, every ink token meets its WCAG contrast:
# text 4.5:1, non-text parts 3:1, as exact rationals
law theme_shipped_legible:
  for s: T.Shipped
  {T.legible(T.table(s)) == True{} : Bool}

# LAW: in every shipped theme, the status colors (accent, success,
# warning, error) stay pairwise distinct in a 256-color terminal
law theme_shipped_status_distinct:
  for s: T.Shipped
  {T.status_distinct(T.table(s)) == True{} : Bool}

# (T1) Color text, value resolution, file reading, completion, picking
# ---------------------------------------------------------------------
# The rules of crates/eukhe-theme that the user sees: which text is a
# color, how a value follows the variables, the error a broken file
# reports (one per kind, never a default), the palette a file completes
# to, and the theme a name picks with its warnings. Requirements:
# R1 a color is "" (the terminal default), an integer 0-255 (an xterm-256
#    index) or #rrggbb (either case); every other value is an error that
#    names it: "Invalid hex color" for a #-string, "Invalid color value"
#    for the rest.
# R2 any other string names a variable; a missing one is "Variable
#    reference not found: <name>", the first one met twice on the chain is
#    "Circular variable reference detected: <name>".
# R3 a file reports the first error of its colors in key order (a key
#    that names no token: "unknown color token"), then the required tokens
#    it does not write, in token order, then the errors of its export
#    page, card and info backgrounds, in that order.
# R4 a file that reads completes: written tokens keep their value, mdBody
#    falls back to text, the refinement pair and foreground to the
#    builtin of the file's mode, the background to the file's background,
#    export page, user-message surface, default theme's background.
# R5 a name picks as the laws above say; a name that picks no theme
#    warns with the first file that did not load and advertises it (or,
#    no theme object, is named after it); every other file that did not
#    load warns once; a valid file whose name an earlier valid file has
#    clashes with the first of them.
# A1 Rust decodes the JSON (serde) and projects it losslessly: keys in
#    order, each string with the index of the variable it names, numbers
#    and other values as JSON writes them (the projection is glue the
#    Rust tests check, the laws cannot see it).

# x is in xs
def th.mem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(Nat.is_eq(y, x), th.mem(rest, x))

def th.val(m: Maybe<&2, T.Var>) -> Maybe<&2, T.Json>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case T.Var{nm, j}:
          Some{j}

# the value of variable i
def th.var(+xs: List<&2, T.Var>, i: Nat) -> Maybe<&2, T.Json>:
  th.val(List.get(&2, T.Var, xs, i))

def th.hex(m: Maybe<&2, Co.Rgb>, s: String) -> T.Got:
  match m:
    case None{}:
      T.Miss{T.BadHex{s}}
    case Some{c}:
      T.Hit{T.Hex{c}}

def th.num(m: Maybe<&2, U32>, s: String) -> T.Got:
  match m:
    case None{}:
      T.Miss{T.BadValue{s}}
    case Some{i}:
      T.Hit{T.Idx{i}}

# a name met before is a cycle; else a missing variable, else its value
def th.ref(looped: Bool, found: Maybe<&2, T.Json>, seen: List<&2, Nat>, s: String, i: Nat) -> T.Step:
  match looped:
    case True{}:
      T.Stop{T.Miss{T.Circular{s}}}
    case False{}:
      match found:
        case None{}:
          T.Stop{T.Miss{T.NotFound{s}}}
        case Some{j}:
          T.Go{i <> seen, j}

def th.name(+vars: List<&2, T.Var>, +seen: List<&2, Nat>, s: String, at: Maybe<&2, Nat>) -> T.Step:
  match at:
    case None{}:
      T.Stop{T.Miss{T.NotFound{s}}}
    case Some{+i}:
      th.ref(th.mem(seen, i), th.var(vars, i), seen, s, i)

def th.text.c(sharp: Bool, +vars: List<&2, T.Var>, +seen: List<&2, Nat>, +s: String, at: Maybe<&2, Nat>) -> T.Step:
  match sharp:
    case True{}:
      T.Stop{th.hex(Co.hex(s), s)}
    case False{}:
      th.name(vars, seen, s, at)

def th.text(+vars: List<&2, T.Var>, +seen: List<&2, Nat>, s: String, at: Maybe<&2, Nat>) -> T.Step:
  match s:
    case SNil{}:
      T.Stop{T.Hit{T.Dflt{}}}
    case SCon{+c, rest}:
      th.text.c(Char.is_eq(c, '#'), vars, seen, SCon{c, rest}, at)

# one step of the rule of crates/eukhe-theme (resolve_var_refs, then
# color_value): "" is the terminal default, a #-string must be #rrggbb,
# any other string names a variable (met before on the chain: a cycle;
# missing: not found); a number must be 0-255; anything else is no color
def th.next(+vars: List<&2, T.Var>, +seen: List<&2, Nat>, j: T.Json) -> T.Step:
  match j:
    case T.JStr{s, at}:
      th.text(vars, seen, s, at)
    case T.JNum{+t}:
      T.Stop{th.num(Co.num(t), t)}
    case T.JOther{t}:
      T.Stop{T.Miss{T.BadValue{t}}}

def th.follow(fuel: Nat, +vars: List<&2, T.Var>, st: T.Step) -> T.Got:
  match fuel:
    case 0n:
      match st:
        case T.Stop{g}:
          g
        case T.Go{seen, j}:
          T.Miss{T.Circular{""}}
    case 1n+f:
      match st:
        case T.Stop{g}:
          g
        case T.Go{seen, j}:
          th.follow(f, vars, th.next(vars, seen, j))

# the color a value resolves to: the rule's steps from no variable met;
# each step past the first meets a new variable, so one step more than
# there are variables reaches the end
def th.chase(+vars: List<&2, T.Var>, j: T.Json) -> T.Got:
  th.follow(1n+List.length(&2, T.Var, vars), vars, T.Go{Nil{}, j})

def th.good(r: T.EntR) -> Bool:
  match r:
    case T.Good{e}:
      True{}
    case T.Bad{f}:
      False{}

# every entry of es reads
def th.clean(+vars: List<&2, T.Var>, es: List<&2, T.REnt>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, rest}:
      Bool.and(th.good(T.entry(vars, e)), th.clean(vars, rest))

def th.ent(r: T.EntR) -> T.Ent:
  match r:
    case T.Good{e}:
      e
    case T.Bad{f}:
      T.Ent{0, T.Dflt{}}

# the entries es read (when every one reads)
def th.goods(+vars: List<&2, T.Var>, es: List<&2, T.REnt>) -> List<&2, T.Ent>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, rest}:
      th.ent(T.entry(vars, e)) <> th.goods(vars, rest)

# the tokens every file must write: all but refinementHeader (14),
# refinementSummary (15), mdBody (18), background (57), foreground (58)
def th.required() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56]

def th.keep(keep: Bool, t: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match keep:
    case True{}:
      t <> rest
    case False{}:
      rest

def th.absent.go(+es: List<&2, T.Ent>, ts: List<&2, U32>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      th.keep(Bool.not(Maybe.is_some(&2, T.Val, T.get(es, t))), t, th.absent.go(es, rest))

# the required tokens es does not write, in token order
def th.absent(+es: List<&2, T.Ent>) -> List<&2, U32>:
  th.absent.go(es, th.required())

def th.reqs(ts: List<&2, U32>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      th.keep(T.required(t), t, th.reqs(rest))

def th.hit(g: T.Got) -> Bool:
  match g:
    case T.Hit{v}:
      True{}
    case T.Miss{why}:
      False{}

# an export background that reads: unset, or a color
def th.fine(+vars: List<&2, T.Var>, m: Maybe<&2, T.Json>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{j}:
      th.hit(T.chase(vars, j))

def th.hitc(g: T.Got) -> Maybe<&2, Co.Rgb>:
  match g:
    case T.Hit{v}:
      T.concrete(v)
    case T.Miss{why}:
      None{}

# the color an export background sets: none when unset or ""
def th.bgv(+vars: List<&2, T.Var>, m: Maybe<&2, T.Json>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      th.hitc(T.chase(vars, j))

# the file's own background as #rrggbb: an index or "" is none
def th.own(m: Maybe<&2, T.Val>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case T.Dflt{}:
          None{}
        case T.Idx{i}:
          None{}
        case T.Hex{c}:
          Some{c}

# the files of one source (custom or registered) that load, in order, as
# candidates after the builtins (ids 0..2): the file at index i is 3 + i
def th.cand(l: T.Ld, +custom: Bool, at: Nat) -> List<&2, T.Cand>:
  match l:
    case T.Fine{nm, c}:
      match c:
        case True{}:
          match custom:
            case True{}:
              [T.Cand{nm, True{}, U32.from_nat(Nat.add(3n, at))}]
            case False{}:
              []
        case False{}:
          match custom:
            case True{}:
              []
            case False{}:
              [T.Cand{nm, True{}, U32.from_nat(Nat.add(3n, at))}]
    case T.Broke{nm, st}:
      []

def th.cands(ls: List<&2, T.Ld>, +custom: Bool, +at: Nat) -> List<&2, T.Cand>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      List.append(&2, T.Cand, th.cand(l, custom, at), th.cands(rest, custom, 1n+at))

# the theme a name picks over the files
def th.pick(+ls: List<&2, T.Ld>, +n: String) -> T.Res:
  T.resolve.name(T.sources(th.cands(ls, False{}, 0n), th.cands(ls, True{}, 0n)), n)

def th.same(m: Maybe<&2, String>, +n: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      String.eq(x, n)

# a file that did not load blames name n: it advertises n, or it is no
# theme object and its stem is n
def th.blames(l: T.Ld, +n: String) -> Bool:
  match l:
    case T.Fine{nm, c}:
      False{}
    case T.Broke{nm, st}:
      match nm:
        case Some{x}:
          String.eq(x, n)
        case None{}:
          th.same(st, n)

def th.at.if(hit: Bool, at: Nat, other: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{at}
    case False{}:
      other

# the index of the first file that blames n (the first is at index at)
def th.blame(ls: List<&2, T.Ld>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, rest}:
      th.at.if(th.blames(l, n), at, th.blame(rest, n, 1n+at))

# the skipped failure: the cause of a warning, none without one
def th.skip(w: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match w:
    case True{}:
      m
    case False{}:
      None{}

def th.cause.of(m: Maybe<&2, Nat>) -> T.Cause:
  match m:
    case None{}:
      T.NoTheme{}
    case Some{at}:
      T.FailedAt{at}

def th.is.at(m: Maybe<&2, Nat>, +at: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, at)

def th.broke(l: T.Ld) -> Bool:
  match l:
    case T.Fine{nm, c}:
      False{}
    case T.Broke{nm, st}:
      True{}

def th.keepn(keep: Bool, at: Nat) -> List<&2, Nat>:
  match keep:
    case True{}:
      [at]
    case False{}:
      []

# the indices of the files that did not load, but skip
def th.broken(ls: List<&2, T.Ld>, +skip: Maybe<&2, Nat>, +at: Nat) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      List.append(&2, Nat, th.keepn(Bool.and(th.broke(l), Bool.not(th.is.at(skip, at))), at), th.broken(rest, skip, 1n+at))

def th.named(l: T.Ld, +n: String) -> Bool:
  match l:
    case T.Fine{nm, c}:
      String.eq(nm, n)
    case T.Broke{nm, st}:
      False{}

# the index of the first loaded file named n (the first is at index at)
def th.first(ls: List<&2, T.Ld>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, rest}:
      th.at.if(th.named(l, n), at, th.first(rest, n, 1n+at))

def th.clash.if(same: Bool, w: Nat, at: Nat) -> List<&2, T.Clash>:
  match same:
    case True{}:
      []
    case False{}:
      [T.Clash{at, w}]

def th.clash(m: Maybe<&2, Nat>, +at: Nat) -> List<&2, T.Clash>:
  match m:
    case None{}:
      []
    case Some{+w}:
      th.clash.if(Nat.is_eq(w, at), w, at)

# every loaded file at index i whose name the loaded file at an earlier
# index j has first: Clash{i, j}, in file order
def th.clashes.go(+all: List<&2, T.Ld>, ls: List<&2, T.Ld>, +at: Nat) -> List<&2, T.Clash>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      match l:
        case T.Fine{+nm, c}:
          List.append(&2, T.Clash, th.clash(th.first(all, nm, 0n), at), th.clashes.go(all, rest, 1n+at))
        case T.Broke{nm, st}:
          th.clashes.go(all, rest, 1n+at)

def th.clashes(+ls: List<&2, T.Ld>) -> List<&2, T.Clash>:
  th.clashes.go(ls, ls, 0n)

def th.res(p: T.Pick) -> T.Res:
  match p:
    case T.Pick{r, c, k, b}:
      r

def th.cause(p: T.Pick) -> Maybe<&2, T.Cause>:
  match p:
    case T.Pick{r, c, k, b}:
      c

def th.clashes.of(p: T.Pick) -> List<&2, T.Clash>:
  match p:
    case T.Pick{r, c, k, b}:
      k

def th.broken.of(p: T.Pick) -> List<&2, Nat>:
  match p:
    case T.Pick{r, c, k, b}:
      b

# Values

# LAW R1 R2 a value resolves as the rule says, for every variables and
# value
# EXCLUDES: a chain followed too far or not far enough, a cycle or a
#   missing variable reported as another error or with another name, a
#   malformed color read as a default
law theme_chase_rule:
  for +vars: List<&2, T.Var>
  for +j: T.Json
  {T.chase(vars, j) == th.chase(vars, j) : T.Got}

def th.vs() -> List<&2, T.Var>:
  [T.Var{"a", T.JStr{"b", Some{1n}}}, T.Var{"b", T.JStr{"#102030", None{}}}, T.Var{"c", T.JStr{"c", Some{2n}}}, T.Var{"d", T.JStr{"e", Some{4n}}}, T.Var{"e", T.JStr{"d", Some{3n}}}, T.Var{"f", T.JStr{"d", Some{3n}}}]

# LAW R1 R2 anchors: a chain to a hex color, a self-cycle, a cycle entered
# from a tail (it names where the chain closes), a missing variable, the
# terminal default, an index, malformed values
# EXCLUDES: a rule that names the start of the chain for a cycle, or
#   reports any of these as another error
law theme_chase_example:
  {[T.chase(th.vs(), T.JStr{"a", Some{0n}}), T.chase(th.vs(), T.JStr{"c", Some{2n}}), T.chase(th.vs(), T.JStr{"f", Some{5n}}), T.chase(th.vs(), T.JStr{"zz", None{}}), T.chase(th.vs(), T.JStr{"", None{}}), T.chase(th.vs(), T.JNum{"7"}), T.chase(th.vs(), T.JNum{"300"}), T.chase(th.vs(), T.JStr{"#12345", None{}}), T.chase(th.vs(), T.JOther{"null"})] == [T.Hit{T.Hex{Co.Rgb{16, 32, 48}}}, T.Miss{T.Circular{"c"}}, T.Miss{T.Circular{"d"}}, T.Miss{T.NotFound{"zz"}}, T.Hit{T.Dflt{}}, T.Hit{T.Idx{7}}, T.Miss{T.BadValue{"300"}}, T.Miss{T.BadHex{"#12345"}}, T.Miss{T.BadValue{"null"}}] : List<&2, T.Got>}

# Reading a file

# LAW R3 a color key that names no token is that error
# EXCLUDES: skipping an unknown key
law theme_entry_unknown:
  for +vars: List<&2, T.Var>
  for +k: String
  for +j: T.Json
  {T.entry(vars, T.REnt{k, None{}, j}) == T.Bad{T.Unknown{k}} : T.EntR}

# LAW R3 a token's color is its value resolved
# EXCLUDES: a color stored under another token or with another value
law theme_entry_color:
  for +vars: List<&2, T.Var>
  for +k: String
  for +t: U32
  for +j: T.Json
  for +v: T.Val
  for h: {T.chase(vars, j) == T.Hit{v} : T.Got}
  {T.entry(vars, T.REnt{k, Some{t}, j}) == T.Good{T.Ent{t, v}} : T.EntR}

# LAW R3 a token whose value is no color is that error, under its key
# EXCLUDES: an error that loses its key or its cause
law theme_entry_invalid:
  for +vars: List<&2, T.Var>
  for +k: String
  for +t: U32
  for +j: T.Json
  for +why: T.Why
  for h: {T.chase(vars, j) == T.Miss{why} : T.Got}
  {T.entry(vars, T.REnt{k, Some{t}, j}) == T.Bad{T.InColor{k, why}} : T.EntR}

# LAW R3 a file reports the error of its first color (in key order) that
# does not read, whatever follows
# EXCLUDES: reporting a later error first, or a missing token before a
#   color error
law theme_read_first_error:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +pre: List<&2, T.REnt>
  for +e: T.REnt
  for +post: List<&2, T.REnt>
  for +pg: Maybe<&2, T.Json>
  for +cd: Maybe<&2, T.Json>
  for +io: Maybe<&2, T.Json>
  for +f: T.Fault
  for ok: {th.clean(vars, pre) == True{} : Bool}
  for bad: {T.entry(vars, e) == T.Bad{f} : T.EntR}
  {T.read(T.RFile{nm, vars, List.append(&2, T.REnt, pre, e <> post), pg, cd, io}) == T.Failed{f} : T.Read}

# LAW R3 the model's required tokens are the documented ones
# EXCLUDES: a token made optional or required by mistake
law theme_required_tokens:
  {th.reqs(T.toks()) == th.required() : List<&2, U32>}

# LAW R3 a file whose colors read reports every required token it does
# not write, in token order
# EXCLUDES: reporting only the first missing token, a wrong order, an
#   export error before the missing tokens
law theme_read_missing:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +cols: List<&2, T.REnt>
  for +pg: Maybe<&2, T.Json>
  for +cd: Maybe<&2, T.Json>
  for +io: Maybe<&2, T.Json>
  for +t: U32
  for +ts: List<&2, U32>
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for miss: {th.absent(th.goods(vars, cols)) == t <> ts : List<&2, U32>}
  {T.read(T.RFile{nm, vars, cols, pg, cd, io}) == T.Failed{T.Missing{t <> ts}} : T.Read}

# LAW R3 then an export page that is no color is that error
# EXCLUDES: ignoring a broken export background
law theme_read_page:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +cols: List<&2, T.REnt>
  for +j: T.Json
  for +cd: Maybe<&2, T.Json>
  for +io: Maybe<&2, T.Json>
  for +why: T.Why
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for bad: {T.chase(vars, j) == T.Miss{why} : T.Got}
  {T.read(T.RFile{nm, vars, cols, Some{j}, cd, io}) == T.Failed{T.InExport{T.OnPage{}, why}} : T.Read}

# LAW R3 then an export card that is no color
# EXCLUDES: checking the card before the page, or not at all
law theme_read_card:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +cols: List<&2, T.REnt>
  for +pg: Maybe<&2, T.Json>
  for +j: T.Json
  for +io: Maybe<&2, T.Json>
  for +why: T.Why
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for fine: {th.fine(vars, pg) == True{} : Bool}
  for bad: {T.chase(vars, j) == T.Miss{why} : T.Got}
  {T.read(T.RFile{nm, vars, cols, pg, Some{j}, io}) == T.Failed{T.InExport{T.OnCard{}, why}} : T.Read}

# LAW R3 then an export info background that is no color
# EXCLUDES: checking the info background early, or not at all
law theme_read_info:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +cols: List<&2, T.REnt>
  for +pg: Maybe<&2, T.Json>
  for +cd: Maybe<&2, T.Json>
  for +j: T.Json
  for +why: T.Why
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for fine1: {th.fine(vars, pg) == True{} : Bool}
  for fine2: {th.fine(vars, cd) == True{} : Bool}
  for bad: {T.chase(vars, j) == T.Miss{why} : T.Got}
  {T.read(T.RFile{nm, vars, cols, pg, cd, Some{j}}) == T.Failed{T.InExport{T.OnInfo{}, why}} : T.Read}

# LAW R3 R4 a file with no error reads to its colors and the export
# colors it sets ("" sets none)
# EXCLUDES: dropping or reordering a color, losing the card or info
#   background, an export "" that sets a color
law theme_read_loaded:
  for +nm: String
  for +vars: List<&2, T.Var>
  for +cols: List<&2, T.REnt>
  for +pg: Maybe<&2, T.Json>
  for +cd: Maybe<&2, T.Json>
  for +io: Maybe<&2, T.Json>
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for fine1: {th.fine(vars, pg) == True{} : Bool}
  for fine2: {th.fine(vars, cd) == True{} : Bool}
  for fine3: {th.fine(vars, io) == True{} : Bool}
  {T.read(T.RFile{nm, vars, cols, pg, cd, io}) == T.Loaded{T.Th{nm, th.goods(vars, cols), th.bgv(vars, pg), th.bgv(vars, cd), th.bgv(vars, io)}} : T.Read}

# Completion

# LAW R3 a file that does not read is rejected with its error
# EXCLUDES: a palette for a broken file, a changed error
law theme_parse_rejected:
  for +f: T.RFile
  for +x: T.Fault
  for h: {T.read(f) == T.Failed{x} : T.Read}
  {T.parse(f) == T.Rejected{x} : T.Parsed}

# LAW R4 a file that reads gives its palette, its mode, its own #rrggbb
# background and its export backgrounds
# EXCLUDES: a palette, mode or export color of another file, a declared
#   background from an index
law theme_parse_painted:
  for +f: T.RFile
  for +nm: String
  for +cols: List<&2, T.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  for h: {T.read(f) == T.Loaded{T.Th{nm, cols, pg, cd, io}} : T.Read}
  {T.parse(f) == T.Painted{T.vals(T.palette(T.Th{nm, cols, pg, cd, io})), T.light(T.Th{nm, cols, pg, cd, io}), th.own(T.get(cols, 57)), pg, cd, io} : T.Parsed}

# LAW R4 the palette fills every token in token order
# EXCLUDES: a palette in another order, or that skips a token
law theme_palette_tokens:
  for +nm: String
  for +cols: List<&2, T.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  {T.palette(T.Th{nm, cols, pg, cd, io}) == T.fill.map(cols, T.background(cols, pg), T.toks()) : List<&2, Maybe<&2, T.Val>>}

# LAW R4 a required token keeps the value the file writes
# EXCLUDES: a written color replaced by a default
law theme_fill_required:
  for +cols: List<&2, T.Ent>
  for +bg: Co.Rgb
  for +t: U32
  for r: {T.required(t) == True{} : Bool}
  {T.fill(cols, bg, t) == T.get(cols, t) : Maybe<&2, T.Val>}

# LAW R4 mdBody is its own value, else text's
# EXCLUDES: mdBody without a fallback, or text overriding mdBody
law theme_fill_md:
  for +cols: List<&2, T.Ent>
  for +bg: Co.Rgb
  {T.fill(cols, bg, 18) == T.or(T.Val, T.get(cols, 18), T.get(cols, 9)) : Maybe<&2, T.Val>}

# LAW R4 the refinement pair is its own value, else the builtin of the
# background's mode
# EXCLUDES: a dark default on a light theme, a default over a written value
law theme_fill_refinement:
  for +cols: List<&2, T.Ent>
  for +bg: Co.Rgb
  {[T.fill(cols, bg, 14), T.fill(cols, bg, 15)] == [Some{T.or_else(T.Val, T.get(cols, 14), T.Hex{T.at(T.defaults(Co.light(bg)), 14n)})}, Some{T.or_else(T.Val, T.get(cols, 15), T.Hex{T.at(T.defaults(Co.light(bg)), 15n)})}] : List<&2, Maybe<&2, T.Val>>}

# LAW R4 the background token paints the background; the foreground is
# the file's own color, else the builtin of the background's mode
# EXCLUDES: a terminal default left in the canvas tokens
law theme_fill_canvas:
  for +cols: List<&2, T.Ent>
  for +bg: Co.Rgb
  {[T.fill(cols, bg, 57), T.fill(cols, bg, 58)] == [Some{T.Hex{bg}}, Some{T.Hex{T.or_else(Co.Rgb, T.concrete.of(T.get(cols, 58)), T.at(T.defaults(Co.light(bg)), 58n))}}] : List<&2, Maybe<&2, T.Val>>}

# LAW R4 the builtins whose values fill a file: the default theme for a
# dark background, light for a light one
# EXCLUDES: fallbacks from the wrong builtin
law theme_defaults_shipped:
  {[T.defaults(False{}), T.defaults(True{})] == [T.table(T.Eukhe{}), T.table(T.Light{})] : List<&2, List<&2, Co.Rgb>>}

# LAW R4 the background is the file's own color, else its export page,
# else its user-message surface, else the default theme's background
# EXCLUDES: another order of the fallbacks, a default over a written color
law theme_background_order:
  for +cols: List<&2, T.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  {T.background(cols, pg) == T.or_else(Co.Rgb, T.or(Co.Rgb, T.concrete.of(T.get(cols, 57)), T.or(Co.Rgb, pg, T.concrete.of(T.get(cols, 49)))), T.at(T.table(T.Eukhe{}), 57n)) : Co.Rgb}

# Picking a theme

# LAW R5 the theme a name picks is the resolution over the files that
# load: the registered ones, the builtins, the custom ones
# EXCLUDES: a file that did not load picked, a custom file before a
#   registered one, a file id that is not its index after the builtins
law theme_pick_res:
  for +ls: List<&2, T.Ld>
  for +n: String
  {th.res(T.pick(ls, n)) == th.pick(ls, n) : T.Res}

# LAW R5 a name that picks no theme warns with the first file that blames
# it, else with "not found"
# EXCLUDES: a cause from a later file, a cause that is not the name's
law theme_pick_cause:
  for +ls: List<&2, T.Ld>
  for +n: String
  for +id: U32
  for w: {th.pick(ls, n) == T.Res{id, True{}} : T.Res}
  {th.cause(T.pick(ls, n)) == Some{th.cause.of(th.blame(ls, n, 0n))} : Maybe<&2, T.Cause>}

# LAW R5 a name that picks a theme warns with no cause
# EXCLUDES: a cause reported for a resolved name
law theme_pick_quiet:
  for +ls: List<&2, T.Ld>
  for +n: String
  for +id: U32
  for w: {th.pick(ls, n) == T.Res{id, False{}} : T.Res}
  {th.cause(T.pick(ls, n)) == None{} : Maybe<&2, T.Cause>}

# LAW R5 every file that did not load warns once: in the cause, or in the
# broken list, in file order
# EXCLUDES: a lost or doubled failure
law theme_pick_broken:
  for +ls: List<&2, T.Ld>
  for +n: String
  for +id: U32
  for +w: Bool
  for r: {th.pick(ls, n) == T.Res{id, w} : T.Res}
  {th.broken.of(T.pick(ls, n)) == th.broken(ls, th.skip(w, th.blame(ls, n, 0n)), 0n) : List<&2, Nat>}

# LAW R5 the clashes: every loaded file whose name an earlier loaded file
# has first, with that file, in file order
# EXCLUDES: a lost clash, a clash with the wrong file
law theme_pick_clashes:
  for +ls: List<&2, T.Ld>
  for +n: String
  {th.clashes.of(T.pick(ls, n)) == th.clashes(ls) : List<&2, T.Clash>}

def th.ls() -> List<&2, T.Ld>:
  [T.Fine{"dusk", False{}}, T.Broke{Some{"mist"}, Some{"a"}}, T.Broke{None{}, Some{"mist"}}, T.Fine{"dusk", True{}}]

# LAW R5 anchor: a registered "dusk" shadows a custom one (a clash), a
# broken file named "mist" is the cause for "mist"
# EXCLUDES: a reading of the laws above that the human did not mean
law theme_pick_example:
  {[T.pick(th.ls(), "dusk"), T.pick(th.ls(), "mist")] == [T.Pick{T.Res{3, False{}}, None{}, [T.Clash{3n, 0n}], [1n, 2n]}, T.Pick{T.Res{0, True{}}, Some{T.FailedAt{1n}}, [T.Clash{3n, 0n}], [2n]}] : List<&2, T.Pick>}

# ---- tui_color ----

# LAWS (T3): terminal colors. Each law is an open claim about the model
# in bend/tui_color.bend (with the theme tables of bend/theme.bend);
# PROOF.bend proves them (as Laws.<law>) with the lemmas of
# PROOF.bend section tui_color.

# (T3) Terminal colors
# --------------------
# docs/interface.md "Terminal colors", the model in bend/tui_color.bend:
# the effort ramp, the usage bands and the color roles of
# crates/eukhe-tui. Every input is free: any ramp ends and any ladder
# length, any token count and any window. The bridge test
# crates/eukhe-tui/src/theme/bridge.rs checks that the Rust ramp, the Rust
# bands and the Rust roles equal the model.

# LAW: every color role of the terminal UI resolves in the palette of
# every valid theme file
law tui_roles_resolve:
  for f: T.Th
  for v: {T.valid(f) == True{} : Bool}
  {TC.resolves(T.palette(f), TC.roles()) == True{} : Bool}

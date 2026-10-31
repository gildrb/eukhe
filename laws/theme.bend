# eukhe: the laws of area theme

import Base
import ../bend/color.bend as Co
import ../bend/theme/bundled.bend as TBundled
import ../bend/theme/chase.bend as TChase
import ../bend/theme/choice.bend as TChoice
import ../bend/theme/file.bend as TFile
import ../bend/theme/name.bend as TName
import ../bend/theme/palette.bend as TPalette
import ../bend/theme/reader.bend as TReader
import ../bend/theme/token.bend as TToken
import ../bend/tui_color.bend as TC
import ../bend/ffi_theme.bend as FTh
import ../spec/theme/wire.bend as Tw
import ../spec/theme/read.bend as Tr
import ../spec/theme/rules.bend as Ts

# ---- themes ----

# LAWS (T1): themes. Each law is an open claim about the models in
# bend/theme/ and bend/color.bend; PROOF.bend proves them (as
# Theme.<law>) with the lemmas of proof/theme/.

# (T1) Themes
# -----------
# docs/interface.md "Themes", the model in bend/theme/: the one theme
# validator and name resolver the terminal UI and the HTML export share,
# run by the compiled entry bend/ffi_theme.bend (section "The compiled
# entry" below); crates/eukhe-theme reads the files and decodes their
# JSON. Every input is free: any registered, builtin and custom
# candidates in any order, valid or not; any name; any theme file (any
# colors, variables and export page). The shipped themes are the tables
# of bend/theme/bundled.bend; a Rust test (crates/eukhe-core,
# theme_rules.rs) checks that the bundled files
# crates/eukhe-theme/themes/*.json paint them.

# LAW theme_resolve_empty: the empty name resolves to the default theme, with no warning
law theme_resolve_empty:
  for src: List<&2, TName.Cand>
  {TName.resolve.name(src, "") == TName.Res{TName.dflt(), False{}} : TName.Res}

# LAW theme_resolve_first: a name resolves to the first valid theme that advertises it, with
# no warning: a registered file before a builtin before a custom file
law theme_resolve_first:
  for +pre: List<&2, TName.Cand>
  for +nm: String
  for +id: U32
  for +post: List<&2, TName.Cand>
  for +n: String
  for ne: {String.is_empty(n) == False{} : Bool}
  for miss: {TName.hit(pre, n) == False{} : Bool}
  for same: {String.eq(nm, n) == True{} : Bool}
  {TName.resolve.name(List.append(&2, TName.Cand, pre, TName.Cand{nm, True{}, id} <> post), n) == TName.Res{id, False{}} : TName.Res}

# LAW theme_resolve_missing: a name that no valid theme advertises (missing, or only in invalid
# files) resolves to the default theme, with a warning: resolution never
# fails
law theme_resolve_missing:
  for +src: List<&2, TName.Cand>
  for +n: String
  for ne: {String.is_empty(n) == False{} : Bool}
  for miss: {TName.hit(src, n) == False{} : Bool}
  {TName.resolve.name(src, n) == TName.Res{TName.dflt(), True{}} : TName.Res}

# LAW theme_load_valid: a theme file loads only when it is valid (every color resolves and
# every required token is written)
law theme_load_valid:
  for r: TFile.RFile
  for -f: TFile.Th
  for loaded: {TReader.load(r) == Some{f} : Maybe<&2, TFile.Th>}
  {TToken.valid(f) == True{} : Bool}

# LAW theme_tokens_complete: the palette of a valid theme file defines every token
law theme_tokens_complete:
  for f: TFile.Th
  for v: {TToken.valid(f) == True{} : Bool}
  {TPalette.complete(TPalette.palette(f)) == True{} : Bool}

# LAW theme_mode_background: two theme files with the same background have the same mode, light
# or dark
law theme_mode_background:
  for f: TFile.Th
  for g: TFile.Th
  for same: {TPalette.bg(f) == TPalette.bg(g) : Co.Rgb}
  {TPalette.light(f) == TPalette.light(g) : Bool}

# LAW theme_palette_name_free: the name of a theme file never changes its palette
law theme_palette_name_free:
  for f: TFile.Th
  for n: String
  {TPalette.palette(TPalette.rename(f, n)) == TPalette.palette(f) : List<&2, Maybe<&2, TFile.Val>>}

# LAW theme_mode_name_free: the name of a theme file never changes its mode
law theme_mode_name_free:
  for f: TFile.Th
  for n: String
  {TPalette.light(TPalette.rename(f, n)) == TPalette.light(f) : Bool}

# LAW theme_shipped_legible: in every shipped theme, every ink token meets its WCAG contrast:
# text 4.5:1, non-text parts 3:1, as exact rationals
law theme_shipped_legible:
  for s: TBundled.Shipped
  {TBundled.legible(TBundled.table(s)) == True{} : Bool}

# LAW theme_shipped_status_distinct: in every shipped theme, the status colors (accent, success,
# warning, error) stay pairwise distinct in a 256-color terminal
law theme_shipped_status_distinct:
  for s: TBundled.Shipped
  {TBundled.status_distinct(TBundled.table(s)) == True{} : Bool}

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

def th.val(m: Maybe<&2, TFile.Var>) -> Maybe<&2, TFile.Json>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case TFile.Var{nm, j}:
          Some{j}

# the value of variable i
def th.var(+xs: List<&2, TFile.Var>, i: Nat) -> Maybe<&2, TFile.Json>:
  th.val(List.get(&2, TFile.Var, xs, i))

def th.hex(m: Maybe<&2, Co.Rgb>, s: String) -> TChase.Got:
  match m:
    case None{}:
      TChase.Miss{TFile.BadHex{s}}
    case Some{c}:
      TChase.Hit{TFile.Hex{c}}

def th.num(m: Maybe<&2, U32>, s: String) -> TChase.Got:
  match m:
    case None{}:
      TChase.Miss{TFile.BadValue{s}}
    case Some{i}:
      TChase.Hit{TFile.Idx{i}}

# a name met before is a cycle; else a missing variable, else its value
def th.ref(looped: Bool, found: Maybe<&2, TFile.Json>, seen: List<&2, Nat>, s: String, i: Nat) -> TChase.Step:
  match looped:
    case True{}:
      TChase.Stop{TChase.Miss{TFile.Circular{s}}}
    case False{}:
      match found:
        case None{}:
          TChase.Stop{TChase.Miss{TFile.NotFound{s}}}
        case Some{j}:
          TChase.Go{i <> seen, j}

def th.name(+vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, s: String, at: Maybe<&2, Nat>) -> TChase.Step:
  match at:
    case None{}:
      TChase.Stop{TChase.Miss{TFile.NotFound{s}}}
    case Some{+i}:
      th.ref(th.mem(seen, i), th.var(vars, i), seen, s, i)

def th.text.c(sharp: Bool, +vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, +s: String, at: Maybe<&2, Nat>) -> TChase.Step:
  match sharp:
    case True{}:
      TChase.Stop{th.hex(Co.hex(s), s)}
    case False{}:
      th.name(vars, seen, s, at)

def th.text(+vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, s: String, at: Maybe<&2, Nat>) -> TChase.Step:
  match s:
    case SNil{}:
      TChase.Stop{TChase.Hit{TFile.Dflt{}}}
    case SCon{+c, rest}:
      th.text.c(Char.is_eq(c, '#'), vars, seen, SCon{c, rest}, at)

# one step of the rule of crates/eukhe-theme (resolve_var_refs, then
# color_value): "" is the terminal default, a #-string must be #rrggbb,
# any other string names a variable (met before on the chain: a cycle;
# missing: not found); a number must be 0-255; anything else is no color
def th.next(+vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, j: TFile.Json) -> TChase.Step:
  match j:
    case TFile.JStr{s, at}:
      th.text(vars, seen, s, at)
    case TFile.JNum{+t}:
      TChase.Stop{th.num(Co.num(t), t)}
    case TFile.JOther{t}:
      TChase.Stop{TChase.Miss{TFile.BadValue{t}}}

def th.follow(fuel: Nat, +vars: List<&2, TFile.Var>, st: TChase.Step) -> TChase.Got:
  match fuel:
    case 0n:
      match st:
        case TChase.Stop{g}:
          g
        case TChase.Go{seen, j}:
          TChase.Miss{TFile.Circular{""}}
    case 1n+f:
      match st:
        case TChase.Stop{g}:
          g
        case TChase.Go{seen, j}:
          th.follow(f, vars, th.next(vars, seen, j))

# the color a value resolves to: the rule's steps from no variable met;
# each step past the first meets a new variable, so one step more than
# there are variables reaches the end
def th.chase(+vars: List<&2, TFile.Var>, j: TFile.Json) -> TChase.Got:
  th.follow(1n+List.length(&2, TFile.Var, vars), vars, TChase.Go{Nil{}, j})

def th.good(r: TReader.EntR) -> Bool:
  match r:
    case TReader.Good{e}:
      True{}
    case TReader.Bad{f}:
      False{}

# every entry of es reads
def th.clean(+vars: List<&2, TFile.Var>, es: List<&2, TFile.REnt>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, rest}:
      Bool.and(th.good(TReader.entry(vars, e)), th.clean(vars, rest))

def th.ent(r: TReader.EntR) -> TFile.Ent:
  match r:
    case TReader.Good{e}:
      e
    case TReader.Bad{f}:
      TFile.Ent{0, TFile.Dflt{}}

# the entries es read (when every one reads)
def th.goods(+vars: List<&2, TFile.Var>, es: List<&2, TFile.REnt>) -> List<&2, TFile.Ent>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, rest}:
      th.ent(TReader.entry(vars, e)) <> th.goods(vars, rest)

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

def th.absent.go(+es: List<&2, TFile.Ent>, ts: List<&2, U32>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      th.keep(Bool.not(Maybe.is_some(&2, TFile.Val, TToken.get(es, t))), t, th.absent.go(es, rest))

# the required tokens es does not write, in token order
def th.absent(+es: List<&2, TFile.Ent>) -> List<&2, U32>:
  th.absent.go(es, th.required())

def th.reqs(ts: List<&2, U32>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      th.keep(TReader.required(t), t, th.reqs(rest))

def th.hit(g: TChase.Got) -> Bool:
  match g:
    case TChase.Hit{v}:
      True{}
    case TChase.Miss{why}:
      False{}

# an export background that reads: unset, or a color
def th.fine(+vars: List<&2, TFile.Var>, m: Maybe<&2, TFile.Json>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{j}:
      th.hit(TChase.chase(vars, j))

def th.hitc(g: TChase.Got) -> Maybe<&2, Co.Rgb>:
  match g:
    case TChase.Hit{v}:
      TToken.concrete(v)
    case TChase.Miss{why}:
      None{}

# the color an export background sets: none when unset or ""
def th.bgv(+vars: List<&2, TFile.Var>, m: Maybe<&2, TFile.Json>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      th.hitc(TChase.chase(vars, j))

# the file's own background as #rrggbb: an index or "" is none
def th.own(m: Maybe<&2, TFile.Val>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case TFile.Dflt{}:
          None{}
        case TFile.Idx{i}:
          None{}
        case TFile.Hex{c}:
          Some{c}

# the files of one source (custom or registered) that load, in order, as
# candidates after the builtins (ids 0..2): the file at index i is 3 + i
def th.cand(l: TChoice.Ld, +custom: Bool, at: Nat) -> List<&2, TName.Cand>:
  match l:
    case TChoice.Fine{nm, c}:
      match c:
        case True{}:
          match custom:
            case True{}:
              [TName.Cand{nm, True{}, U32.from_nat(Nat.add(3n, at))}]
            case False{}:
              []
        case False{}:
          match custom:
            case True{}:
              []
            case False{}:
              [TName.Cand{nm, True{}, U32.from_nat(Nat.add(3n, at))}]
    case TChoice.Broke{nm, st}:
      []

def th.cands(ls: List<&2, TChoice.Ld>, +custom: Bool, +at: Nat) -> List<&2, TName.Cand>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      List.append(&2, TName.Cand, th.cand(l, custom, at), th.cands(rest, custom, 1n+at))

# the theme a name picks over the files
def th.pick(+ls: List<&2, TChoice.Ld>, +n: String) -> TName.Res:
  TName.resolve.name(TName.sources(th.cands(ls, False{}, 0n), th.cands(ls, True{}, 0n)), n)

def th.same(m: Maybe<&2, String>, +n: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      String.eq(x, n)

# a file that did not load blames name n: it advertises n, or it is no
# theme object and its stem is n
def th.blames(l: TChoice.Ld, +n: String) -> Bool:
  match l:
    case TChoice.Fine{nm, c}:
      False{}
    case TChoice.Broke{nm, st}:
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
def th.blame(ls: List<&2, TChoice.Ld>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
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

def th.cause.of(m: Maybe<&2, Nat>) -> TChoice.Cause:
  match m:
    case None{}:
      TChoice.NoTheme{}
    case Some{at}:
      TChoice.FailedAt{at}

def th.is.at(m: Maybe<&2, Nat>, +at: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, at)

def th.broke(l: TChoice.Ld) -> Bool:
  match l:
    case TChoice.Fine{nm, c}:
      False{}
    case TChoice.Broke{nm, st}:
      True{}

def th.keepn(keep: Bool, at: Nat) -> List<&2, Nat>:
  match keep:
    case True{}:
      [at]
    case False{}:
      []

# the indices of the files that did not load, but skip
def th.broken(ls: List<&2, TChoice.Ld>, +skip: Maybe<&2, Nat>, +at: Nat) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      List.append(&2, Nat, th.keepn(Bool.and(th.broke(l), Bool.not(th.is.at(skip, at))), at), th.broken(rest, skip, 1n+at))

def th.named(l: TChoice.Ld, +n: String) -> Bool:
  match l:
    case TChoice.Fine{nm, c}:
      String.eq(nm, n)
    case TChoice.Broke{nm, st}:
      False{}

# the index of the first loaded file named n (the first is at index at)
def th.first(ls: List<&2, TChoice.Ld>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, rest}:
      th.at.if(th.named(l, n), at, th.first(rest, n, 1n+at))

def th.clash.if(same: Bool, w: Nat, at: Nat) -> List<&2, TChoice.Clash>:
  match same:
    case True{}:
      []
    case False{}:
      [TChoice.Clash{at, w}]

def th.clash(m: Maybe<&2, Nat>, +at: Nat) -> List<&2, TChoice.Clash>:
  match m:
    case None{}:
      []
    case Some{+w}:
      th.clash.if(Nat.is_eq(w, at), w, at)

# every loaded file at index i whose name the loaded file at an earlier
# index j has first: Clash{i, j}, in file order
def th.clashes.go(+all: List<&2, TChoice.Ld>, ls: List<&2, TChoice.Ld>, +at: Nat) -> List<&2, TChoice.Clash>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      match l:
        case TChoice.Fine{+nm, c}:
          List.append(&2, TChoice.Clash, th.clash(th.first(all, nm, 0n), at), th.clashes.go(all, rest, 1n+at))
        case TChoice.Broke{nm, st}:
          th.clashes.go(all, rest, 1n+at)

def th.clashes(+ls: List<&2, TChoice.Ld>) -> List<&2, TChoice.Clash>:
  th.clashes.go(ls, ls, 0n)

def th.res(p: TChoice.Pick) -> TName.Res:
  match p:
    case TChoice.Pick{r, c, k, b}:
      r

def th.cause(p: TChoice.Pick) -> Maybe<&2, TChoice.Cause>:
  match p:
    case TChoice.Pick{r, c, k, b}:
      c

def th.clashes.of(p: TChoice.Pick) -> List<&2, TChoice.Clash>:
  match p:
    case TChoice.Pick{r, c, k, b}:
      k

def th.broken.of(p: TChoice.Pick) -> List<&2, Nat>:
  match p:
    case TChoice.Pick{r, c, k, b}:
      b

# Values

# LAW theme_chase_rule (R1): R2 a value resolves as the rule says, for every variables and
# value
# EXCLUDES: a chain followed too far or not far enough, a cycle or a
#   missing variable reported as another error or with another name, a
#   malformed color read as a default
law theme_chase_rule:
  for +vars: List<&2, TFile.Var>
  for +j: TFile.Json
  {TChase.chase(vars, j) == th.chase(vars, j) : TChase.Got}

def th.vs() -> List<&2, TFile.Var>:
  [TFile.Var{"a", TFile.JStr{"b", Some{1n}}}, TFile.Var{"b", TFile.JStr{"#102030", None{}}}, TFile.Var{"c", TFile.JStr{"c", Some{2n}}}, TFile.Var{"d", TFile.JStr{"e", Some{4n}}}, TFile.Var{"e", TFile.JStr{"d", Some{3n}}}, TFile.Var{"f", TFile.JStr{"d", Some{3n}}}]

# LAW theme_chase_example (R1): R2 anchors: a chain to a hex color, a self-cycle, a cycle entered
# from a tail (it names where the chain closes), a missing variable, the
# terminal default, an index, malformed values
# EXCLUDES: a rule that names the start of the chain for a cycle, or
#   reports any of these as another error
law theme_chase_example:
  {[TChase.chase(th.vs(), TFile.JStr{"a", Some{0n}}), TChase.chase(th.vs(), TFile.JStr{"c", Some{2n}}), TChase.chase(th.vs(), TFile.JStr{"f", Some{5n}}), TChase.chase(th.vs(), TFile.JStr{"zz", None{}}), TChase.chase(th.vs(), TFile.JStr{"", None{}}), TChase.chase(th.vs(), TFile.JNum{"7"}), TChase.chase(th.vs(), TFile.JNum{"300"}), TChase.chase(th.vs(), TFile.JStr{"#12345", None{}}), TChase.chase(th.vs(), TFile.JOther{"null"})] == [TChase.Hit{TFile.Hex{Co.Rgb{16, 32, 48}}}, TChase.Miss{TFile.Circular{"c"}}, TChase.Miss{TFile.Circular{"d"}}, TChase.Miss{TFile.NotFound{"zz"}}, TChase.Hit{TFile.Dflt{}}, TChase.Hit{TFile.Idx{7}}, TChase.Miss{TFile.BadValue{"300"}}, TChase.Miss{TFile.BadHex{"#12345"}}, TChase.Miss{TFile.BadValue{"null"}}] : List<&2, TChase.Got>}

# Reading a file

# LAW theme_entry_unknown (R3): a color key that names no token is that error
# EXCLUDES: skipping an unknown key
law theme_entry_unknown:
  for +vars: List<&2, TFile.Var>
  for +k: String
  for +j: TFile.Json
  {TReader.entry(vars, TFile.REnt{k, None{}, j}) == TReader.Bad{TFile.Unknown{k}} : TReader.EntR}

# LAW theme_entry_color (R3): a token's color is its value resolved
# EXCLUDES: a color stored under another token or with another value
law theme_entry_color:
  for +vars: List<&2, TFile.Var>
  for +k: String
  for +t: U32
  for +j: TFile.Json
  for +v: TFile.Val
  for h: {TChase.chase(vars, j) == TChase.Hit{v} : TChase.Got}
  {TReader.entry(vars, TFile.REnt{k, Some{t}, j}) == TReader.Good{TFile.Ent{t, v}} : TReader.EntR}

# LAW theme_entry_invalid (R3): a token whose value is no color is that error, under its key
# EXCLUDES: an error that loses its key or its cause
law theme_entry_invalid:
  for +vars: List<&2, TFile.Var>
  for +k: String
  for +t: U32
  for +j: TFile.Json
  for +why: TFile.Why
  for h: {TChase.chase(vars, j) == TChase.Miss{why} : TChase.Got}
  {TReader.entry(vars, TFile.REnt{k, Some{t}, j}) == TReader.Bad{TFile.InColor{k, why}} : TReader.EntR}

# LAW theme_read_first_error (R3): a file reports the error of its first color (in key order) that
# does not read, whatever follows
# EXCLUDES: reporting a later error first, or a missing token before a
#   color error
law theme_read_first_error:
  for +nm: String
  for +vars: List<&2, TFile.Var>
  for +pre: List<&2, TFile.REnt>
  for +e: TFile.REnt
  for +post: List<&2, TFile.REnt>
  for +pg: Maybe<&2, TFile.Json>
  for +cd: Maybe<&2, TFile.Json>
  for +io: Maybe<&2, TFile.Json>
  for +f: TFile.Fault
  for ok: {th.clean(vars, pre) == True{} : Bool}
  for bad: {TReader.entry(vars, e) == TReader.Bad{f} : TReader.EntR}
  {TReader.read(TFile.RFile{nm, vars, List.append(&2, TFile.REnt, pre, e <> post), pg, cd, io}) == TReader.Failed{f} : TReader.Read}

# LAW theme_required_tokens (R3): the model's required tokens are the documented ones
# EXCLUDES: a token made optional or required by mistake
law theme_required_tokens:
  {th.reqs(TToken.toks()) == th.required() : List<&2, U32>}

# LAW theme_read_missing (R3): a file whose colors read reports every required token it does
# not write, in token order
# EXCLUDES: reporting only the first missing token, a wrong order, an
#   export error before the missing tokens
law theme_read_missing:
  for +nm: String
  for +vars: List<&2, TFile.Var>
  for +cols: List<&2, TFile.REnt>
  for +pg: Maybe<&2, TFile.Json>
  for +cd: Maybe<&2, TFile.Json>
  for +io: Maybe<&2, TFile.Json>
  for +t: U32
  for +ts: List<&2, U32>
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for miss: {th.absent(th.goods(vars, cols)) == t <> ts : List<&2, U32>}
  {TReader.read(TFile.RFile{nm, vars, cols, pg, cd, io}) == TReader.Failed{TFile.Missing{t <> ts}} : TReader.Read}

# LAW theme_read_page (R3): then an export page that is no color is that error
# EXCLUDES: ignoring a broken export background
law theme_read_page:
  for +nm: String
  for +vars: List<&2, TFile.Var>
  for +cols: List<&2, TFile.REnt>
  for +j: TFile.Json
  for +cd: Maybe<&2, TFile.Json>
  for +io: Maybe<&2, TFile.Json>
  for +why: TFile.Why
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for bad: {TChase.chase(vars, j) == TChase.Miss{why} : TChase.Got}
  {TReader.read(TFile.RFile{nm, vars, cols, Some{j}, cd, io}) == TReader.Failed{TFile.InExport{TFile.OnPage{}, why}} : TReader.Read}

# LAW theme_read_card (R3): then an export card that is no color
# EXCLUDES: checking the card before the page, or not at all
law theme_read_card:
  for +nm: String
  for +vars: List<&2, TFile.Var>
  for +cols: List<&2, TFile.REnt>
  for +pg: Maybe<&2, TFile.Json>
  for +j: TFile.Json
  for +io: Maybe<&2, TFile.Json>
  for +why: TFile.Why
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for fine: {th.fine(vars, pg) == True{} : Bool}
  for bad: {TChase.chase(vars, j) == TChase.Miss{why} : TChase.Got}
  {TReader.read(TFile.RFile{nm, vars, cols, pg, Some{j}, io}) == TReader.Failed{TFile.InExport{TFile.OnCard{}, why}} : TReader.Read}

# LAW theme_read_info (R3): then an export info background that is no color
# EXCLUDES: checking the info background early, or not at all
law theme_read_info:
  for +nm: String
  for +vars: List<&2, TFile.Var>
  for +cols: List<&2, TFile.REnt>
  for +pg: Maybe<&2, TFile.Json>
  for +cd: Maybe<&2, TFile.Json>
  for +j: TFile.Json
  for +why: TFile.Why
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for fine1: {th.fine(vars, pg) == True{} : Bool}
  for fine2: {th.fine(vars, cd) == True{} : Bool}
  for bad: {TChase.chase(vars, j) == TChase.Miss{why} : TChase.Got}
  {TReader.read(TFile.RFile{nm, vars, cols, pg, cd, Some{j}}) == TReader.Failed{TFile.InExport{TFile.OnInfo{}, why}} : TReader.Read}

# LAW theme_read_loaded (R3): R4 a file with no error reads to its colors and the export
# colors it sets ("" sets none)
# EXCLUDES: dropping or reordering a color, losing the card or info
#   background, an export "" that sets a color
law theme_read_loaded:
  for +nm: String
  for +vars: List<&2, TFile.Var>
  for +cols: List<&2, TFile.REnt>
  for +pg: Maybe<&2, TFile.Json>
  for +cd: Maybe<&2, TFile.Json>
  for +io: Maybe<&2, TFile.Json>
  for ok: {th.clean(vars, cols) == True{} : Bool}
  for all: {th.absent(th.goods(vars, cols)) == [] : List<&2, U32>}
  for fine1: {th.fine(vars, pg) == True{} : Bool}
  for fine2: {th.fine(vars, cd) == True{} : Bool}
  for fine3: {th.fine(vars, io) == True{} : Bool}
  {TReader.read(TFile.RFile{nm, vars, cols, pg, cd, io}) == TReader.Loaded{TFile.Th{nm, th.goods(vars, cols), th.bgv(vars, pg), th.bgv(vars, cd), th.bgv(vars, io)}} : TReader.Read}

# Completion

# LAW theme_parse_rejected (R3): a file that does not read is rejected with its error
# EXCLUDES: a palette for a broken file, a changed error
law theme_parse_rejected:
  for +f: TFile.RFile
  for +x: TFile.Fault
  for h: {TReader.read(f) == TReader.Failed{x} : TReader.Read}
  {TPalette.parse(f) == TPalette.Rejected{x} : TPalette.Parsed}

# LAW theme_parse_painted (R4): a file that reads gives its palette, its mode, its own #rrggbb
# background and its export backgrounds
# EXCLUDES: a palette, mode or export color of another file, a declared
#   background from an index
law theme_parse_painted:
  for +f: TFile.RFile
  for +nm: String
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  for h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}
  {TPalette.parse(f) == TPalette.Painted{TPalette.vals(TPalette.palette(TFile.Th{nm, cols, pg, cd, io})), TPalette.light(TFile.Th{nm, cols, pg, cd, io}), th.own(TToken.get(cols, 57)), pg, cd, io} : TPalette.Parsed}

# LAW theme_palette_tokens (R4): the palette fills every token in token order
# EXCLUDES: a palette in another order, or that skips a token
law theme_palette_tokens:
  for +nm: String
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  {TPalette.palette(TFile.Th{nm, cols, pg, cd, io}) == TPalette.fill.map(cols, TPalette.background(cols, pg), TToken.toks()) : List<&2, Maybe<&2, TFile.Val>>}

# LAW theme_fill_required (R4): a required token keeps the value the file writes
# EXCLUDES: a written color replaced by a default
law theme_fill_required:
  for +cols: List<&2, TFile.Ent>
  for +bg: Co.Rgb
  for +t: U32
  for r: {TReader.required(t) == True{} : Bool}
  {TPalette.fill(cols, bg, t) == TToken.get(cols, t) : Maybe<&2, TFile.Val>}

# LAW theme_fill_md (R4): mdBody is its own value, else text's
# EXCLUDES: mdBody without a fallback, or text overriding mdBody
law theme_fill_md:
  for +cols: List<&2, TFile.Ent>
  for +bg: Co.Rgb
  {TPalette.fill(cols, bg, 18) == TPalette.or(TFile.Val, TToken.get(cols, 18), TToken.get(cols, 9)) : Maybe<&2, TFile.Val>}

# LAW theme_fill_refinement (R4): the refinement pair is its own value, else the builtin of the
# background's mode
# EXCLUDES: a dark default on a light theme, a default over a written value
law theme_fill_refinement:
  for +cols: List<&2, TFile.Ent>
  for +bg: Co.Rgb
  {[TPalette.fill(cols, bg, 14), TPalette.fill(cols, bg, 15)] == [Some{TPalette.or_else(TFile.Val, TToken.get(cols, 14), TFile.Hex{TPalette.at(TPalette.defaults(Co.light(bg)), 14n)})}, Some{TPalette.or_else(TFile.Val, TToken.get(cols, 15), TFile.Hex{TPalette.at(TPalette.defaults(Co.light(bg)), 15n)})}] : List<&2, Maybe<&2, TFile.Val>>}

# LAW theme_fill_canvas (R4): the background token paints the background; the foreground is
# the file's own color, else the builtin of the background's mode
# EXCLUDES: a terminal default left in the canvas tokens
law theme_fill_canvas:
  for +cols: List<&2, TFile.Ent>
  for +bg: Co.Rgb
  {[TPalette.fill(cols, bg, 57), TPalette.fill(cols, bg, 58)] == [Some{TFile.Hex{bg}}, Some{TFile.Hex{TPalette.or_else(Co.Rgb, TPalette.concrete.of(TToken.get(cols, 58)), TPalette.at(TPalette.defaults(Co.light(bg)), 58n))}}] : List<&2, Maybe<&2, TFile.Val>>}

# LAW theme_defaults_shipped (R4): the builtins whose values fill a file: the default theme for a
# dark background, light for a light one
# EXCLUDES: fallbacks from the wrong builtin
law theme_defaults_shipped:
  {[TPalette.defaults(False{}), TPalette.defaults(True{})] == [TBundled.table(TBundled.Eukhe{}), TBundled.table(TBundled.Light{})] : List<&2, List<&2, Co.Rgb>>}

# LAW theme_background_order (R4): the background is the file's own color, else its export page,
# else its user-message surface, else the default theme's background
# EXCLUDES: another order of the fallbacks, a default over a written color
law theme_background_order:
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  {TPalette.background(cols, pg) == TPalette.or_else(Co.Rgb, TPalette.or(Co.Rgb, TPalette.concrete.of(TToken.get(cols, 57)), TPalette.or(Co.Rgb, pg, TPalette.concrete.of(TToken.get(cols, 49)))), TPalette.at(TBundled.table(TBundled.Eukhe{}), 57n)) : Co.Rgb}

# Picking a theme

# LAW theme_pick_res (R5): the theme a name picks is the resolution over the files that
# load: the registered ones, the builtins, the custom ones
# EXCLUDES: a file that did not load picked, a custom file before a
#   registered one, a file id that is not its index after the builtins
law theme_pick_res:
  for +ls: List<&2, TChoice.Ld>
  for +n: String
  {th.res(TChoice.pick(ls, n)) == th.pick(ls, n) : TName.Res}

# LAW theme_pick_cause (R5): a name that picks no theme warns with the first file that blames
# it, else with "not found"
# EXCLUDES: a cause from a later file, a cause that is not the name's
law theme_pick_cause:
  for +ls: List<&2, TChoice.Ld>
  for +n: String
  for +id: U32
  for w: {th.pick(ls, n) == TName.Res{id, True{}} : TName.Res}
  {th.cause(TChoice.pick(ls, n)) == Some{th.cause.of(th.blame(ls, n, 0n))} : Maybe<&2, TChoice.Cause>}

# LAW theme_pick_quiet (R5): a name that picks a theme warns with no cause
# EXCLUDES: a cause reported for a resolved name
law theme_pick_quiet:
  for +ls: List<&2, TChoice.Ld>
  for +n: String
  for +id: U32
  for w: {th.pick(ls, n) == TName.Res{id, False{}} : TName.Res}
  {th.cause(TChoice.pick(ls, n)) == None{} : Maybe<&2, TChoice.Cause>}

# LAW theme_pick_broken (R5): every file that did not load warns once: in the cause, or in the
# broken list, in file order
# EXCLUDES: a lost or doubled failure
law theme_pick_broken:
  for +ls: List<&2, TChoice.Ld>
  for +n: String
  for +id: U32
  for +w: Bool
  for r: {th.pick(ls, n) == TName.Res{id, w} : TName.Res}
  {th.broken.of(TChoice.pick(ls, n)) == th.broken(ls, th.skip(w, th.blame(ls, n, 0n)), 0n) : List<&2, Nat>}

# LAW theme_pick_clashes (R5): the clashes: every loaded file whose name an earlier loaded file
# has first, with that file, in file order
# EXCLUDES: a lost clash, a clash with the wrong file
law theme_pick_clashes:
  for +ls: List<&2, TChoice.Ld>
  for +n: String
  {th.clashes.of(TChoice.pick(ls, n)) == th.clashes(ls) : List<&2, TChoice.Clash>}

def th.ls() -> List<&2, TChoice.Ld>:
  [TChoice.Fine{"dusk", False{}}, TChoice.Broke{Some{"mist"}, Some{"a"}}, TChoice.Broke{None{}, Some{"mist"}}, TChoice.Fine{"dusk", True{}}]

# LAW theme_pick_example (R5): anchor: a registered "dusk" shadows a custom one (a clash), a
# broken file named "mist" is the cause for "mist"
# EXCLUDES: a reading of the laws above that the human did not mean
law theme_pick_example:
  {[TChoice.pick(th.ls(), "dusk"), TChoice.pick(th.ls(), "mist")] == [TChoice.Pick{TName.Res{3, False{}}, None{}, [TChoice.Clash{3n, 0n}], [1n, 2n]}, TChoice.Pick{TName.Res{0, True{}}, Some{TChoice.FailedAt{1n}}, [TChoice.Clash{3n, 0n}], [2n]}] : List<&2, TChoice.Pick>}

# (T1) The rules' helpers, pinned
# --------------------------------
# The laws above read these helpers of the model; here each is the
# meaning spec/theme/rules.bend states.

# LAW theme_hit_spec (R5): a candidate advertises a name only when it is valid and its name is
# exactly that name
# EXCLUDES: a prefix, case-folded or substring match of a name
law theme_hit_spec:
  for src: List<&2, TName.Cand>
  for +n: String
  {TName.hit(src, n) == Ts.has(src, n) : Bool}

# LAW theme_prefix_example (R5): anchor: "d" names no theme (dark starts with it): the default
# theme, with the warning "not found"
# EXCLUDES: a name matched by prefix
law theme_prefix_example:
  {TChoice.pick([], "d") == TChoice.Pick{TName.Res{0, True{}}, Some{TChoice.NoTheme{}}, [], []} : TChoice.Pick} & {FTh.ffi("1,1,d0,") == "0,T1,1,0,0,0,0," : String}

# LAW theme_concrete_spec (R4): a value paints nothing for the terminal default, its xterm-256
# color for an index, itself for a written color
# EXCLUDES: a file's own background, export page or foreground ignored
law theme_concrete_spec:
  for v: TFile.Val
  {TToken.concrete(v) == Ts.concrete(v) : Maybe<&2, Co.Rgb>}

# LAW theme_light_spec (R4): a file is light when its background is (Co.light), and its
# background is the completed one
# EXCLUDES: a constant mode, a mode from another color than the background
law theme_light_spec:
  for +nm: String
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  {TPalette.light(TFile.Th{nm, cols, pg, cd, io}) == Co.light(TPalette.background(cols, pg)) : Bool} & {TPalette.bg(TFile.Th{nm, cols, pg, cd, io}) == TPalette.background(cols, pg) : Co.Rgb}

# LAW theme_light_example (R4): anchor: a file with a white background is light, one with a
# black background dark
# EXCLUDES: a constant mode
law theme_light_example:
  {[TPalette.light(TFile.Th{"w", [TFile.Ent{57, TFile.Hex{Co.Rgb{255, 255, 255}}}], None{}, None{}, None{}}), TPalette.light(TFile.Th{"b", [TFile.Ent{57, TFile.Hex{Co.Rgb{0, 0, 0}}}], None{}, None{}, None{}})] == [True{}, False{}] : List<&2, Bool>}

# LAW theme_legible_spec (R4): a table is legible exactly when every ink token meets its
# contrast on its surface (the pairs of spec/theme/rules.bend), for every
# table
# EXCLUDES: an empty or shortened pair list, a constant legibility test
#   (theme_shipped_legible made vacuous)
law theme_legible_spec:
  for +xs: List<&2, Co.Rgb>
  {TBundled.legible(xs) == Ts.legible(xs) : Bool}

# LAW theme_status_distinct_spec (R4): the status test is exactly: accent, success, warning and
# error pairwise distinct in a 256-color terminal, for every table
# EXCLUDES: a constant status test (theme_shipped_status_distinct made
#   vacuous), other tokens compared
law theme_status_distinct_spec:
  for +xs: List<&2, Co.Rgb>
  {TBundled.status_distinct(xs) == Ts.status_distinct(xs) : Bool}

# (T1) The compiled entry
# -----------------------
# bend/ffi_theme.bend runs the rules above for Rust
# (crates/eukhe-bend/src/rules/theme.rs; crates/eukhe-theme reads the
# files and decodes their JSON): a theme file read and completed, one
# load (every file the sources reach read, the theme a name picks, the
# clashes that warn, the picked file's palette) and the shipped themes'
# colors. The spellers, the reader and the spec of one load live in
# spec/theme/wire.bend and spec/theme/read.bend, made of the wire
# primitives only (bend/wire.bend, laws/wire.bend). Requirements:
# R6 every request Rust writes (every text, count and variable index
#    within the wire) is answered with the rules' decision: a load with
#    TPalette.parse and the color each token paints (a written color, an
#    index's xterm-256 color, the terminal default the background on a
#    surface and the foreground elsewhere); a resolve with TChoice.pick
#    over the files as they read, only the clashes whose palette differs
#    from the winner's, how each file read, and the picked file's
#    palette; a shipped theme with its table. Any other input gets
#    exactly "E theme: malformed request"; input after a request is never
#    read as part of it.
# Not stated here, by design: that every request the entry accepts holds
# only lengths and counts that fit the wire (the wire's decoders never
# read a 15th digit: laws/wire.bend wire_nat_decoded_fits); and file ids
# past 2^32 (a file is 3 + its index as a U32, in the model and in these
# specs alike): eukhe-theme reads at most 4096 files a load.

# the builtin themes as the candidates a name resolves over: eukhe (the
# default theme, id 0), dark (1) and light (2), all valid
def th.builtins() -> List<&2, TName.Cand>:
  [TName.Cand{"eukhe", True{}, 0}, TName.Cand{"dark", True{}, 1}, TName.Cand{"light", True{}, 2}]

# LAW theme_sources_order (R5): a name resolves over the registered files, then the builtins
# eukhe (0), dark (1), light (2), then the custom directory's files
# EXCLUDES: custom files before the builtins (a custom "light" shadowing
#   the builtin), a builtin renamed, renumbered, dropped or invalid
law theme_sources_order:
  for reg: List<&2, TName.Cand>
  for custom: List<&2, TName.Cand>
  {TName.sources(reg, custom) == List.append(&2, TName.Cand, reg, List.append(&2, TName.Cand, th.builtins(), custom)) : List<&2, TName.Cand>}

# LAW theme_builtin_before_custom_example (R5): anchor: a valid custom file advertising "light" loses to the builtin
# light (id 2) with no warning; a registered one wins (id 3)
# EXCLUDES: custom files resolved before the builtins
law theme_builtin_before_custom_example:
  {[TChoice.pick([TChoice.Fine{"light", True{}}], "light"), TChoice.pick([TChoice.Fine{"light", False{}}], "light")] == [TChoice.Pick{TName.Res{2, False{}}, None{}, [], []}, TChoice.Pick{TName.Res{3, False{}}, None{}, [], []}] : List<&2, TChoice.Pick>}

# LAW theme_ffi_answers (R6): every request Rust writes is answered with the rules' decision,
# spelled as Rust reads it
# EXCLUDES: a field misread, swapped or dropped; a file parsed with
#   another rule; a pick over files other than those read; a clash that
#   warns for the same theme twice, or is quiet for two different ones;
#   a painted color off the default rule; a reply spelled otherwise
law theme_ffi_answers:
  for +r: FTh.Req
  for fits: {Tw.fits(r) == True{} : Bool}
  {FTh.ffi(Tw.req(r, "")) == Tw.answer(r) : String}

# LAW theme_ffi_malformed_exact (R6): every input that is not exactly one request (an unknown tag, a
# short list, a number past the wire, input left over) gets exactly the
# error form "E theme: malformed request"
# EXCLUDES: a default theme or a guessed file for malformed input, a
#   partial reply
law theme_ffi_malformed_exact:
  for +s: String
  for no: {Tr.read(s) == None{} : Maybe<&2, FTh.Req>}
  {FTh.ffi(s) == Tr.refused() : String}

# LAW theme_ffi_left_over (R6): a request followed by more input is refused whole
# EXCLUDES: an entry that answers a prefix of its input and drops the rest
law theme_ffi_left_over:
  for +r: FTh.Req
  for fits: {Tw.fits(r) == True{} : Bool}
  for c: Char
  for x: String
  {FTh.ffi(Tw.req(r, SCon{c, x})) == Tr.refused() : String}

# LAW theme_ffi_example (R6): anchor: the strings Rust sends: a file whose key zz names no
# token, the name "dusk" over a registered file named dusk that is no
# theme object (the default theme, with that file as the cause); an
# unknown tag, input left over and a 15-digit number refused
# EXCLUDES: a reading of the laws above that the human did not mean
law theme_ffi_example:
  {[FTh.ffi("0,1,x0,1,2,zz0,1,1,30,0,0,"), FTh.ffi("1,4,dusk1,F1,4,dusk0,"), FTh.ffi("3,"), FTh.ffi("2,0,x"), FTh.ffi("100000000000000,")] == ["0,0,2,zz", "0,T1,0,0,0,0,1,2,0,", Tr.refused(), Tr.refused(), Tr.refused()] : List<&2, String>}

# ---- tui_color ----

# LAWS (T3): terminal colors. Each law is an open claim about the model
# in bend/tui_color.bend (with the theme tables of bend/theme/bundled.bend);
# PROOF.bend proves them (as TuiColor.<law>) with the lemmas of
# proof/tui_color/.

# (T3) Terminal colors
# --------------------
# docs/interface.md "Terminal colors", the model in bend/tui_color.bend:
# the effort ramp, the usage bands and the color roles of
# crates/eukhe-tui. Every input is free: any ramp ends and any ladder
# length, any token count and any window. The entry bend/ffi_tui_color.bend
# runs the ramp, the bands and the roles; laws/tui_color.bend pins it.

# LAW tui_roles_resolve: every color role of the terminal UI resolves in the palette of
# every valid theme file
law tui_roles_resolve:
  for f: TFile.Th
  for v: {TToken.valid(f) == True{} : Bool}
  {TC.resolves(TPalette.palette(f), TC.roles()) == True{} : Bool}

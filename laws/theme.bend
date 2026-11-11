# eukhe: the laws of area theme
#
# LAWS (T1): themes. Each law is an open claim about the theme rules of
# bend/theme/ (with bend/color.bend) or the compiled entry
# bend/ffi_theme.bend that runs them; PROOF.bend proves them (as
# Theme.<law>) with the lemmas of proof/theme/.
#
# Requirements (crates/eukhe-theme, which follows oh-my-pi
# packages/tui/src/theme: color.ts resolveVarRefs, loader.ts, theme.ts):
# R1 a color is "" (the terminal default), an integer 0-255 (an xterm-256
#    index) or #rrggbb (either case); every other value is an error that
#    names it: "Invalid hex color" for a #-string, "Invalid color value"
#    for the rest. Law: theme_chase_chain (anchor theme_chase_example).
# R2 any other string names a variable; a missing one is "Variable
#    reference not found: <name>", the first one met twice on the chain is
#    "Circular variable reference detected: <name>" (omp color.ts
#    resolveVarRefs). Law: theme_chase_chain.
# R3 a file is rejected with the first error of its colors in key order (a
#    key that names no token: "unknown color token"), then the required
#    tokens it does not write, in token order, then the errors of its
#    export page, card and info backgrounds, in that order. Laws:
#    theme_read_first_error, theme_required_tokens, theme_read_missing,
#    theme_read_page, theme_read_card, theme_read_info; a file with no error
#    reads to its colors: theme_read_loaded, theme_load_valid.
# R4 a file that reads completes to one value per token: written tokens
#    keep their value, mdBody falls back to text, the refinement pair and
#    the foreground to the builtin of the file's mode, the background to
#    the file's background, export page, user-message surface, default
#    theme's background; the mode is light exactly when that background is
#    light. Laws: theme_tokens_complete, theme_parse_tokens,
#    theme_parse_written, theme_parse_md, theme_parse_refinement,
#    theme_parse_foreground, theme_parse_background, theme_parse_mode,
#    theme_parse_declared (anchor theme_light_example). The shipped themes
#    are legible (every ink token meets its WCAG contrast) and keep their
#    status colors apart in a 256-color terminal: theme_shipped_legible,
#    theme_legible_sound, theme_pairs_cover, theme_shipped_status_distinct,
#    theme_status_sound.
# R5 a name picks, among the files that load: the first registered file
#    that advertises it, else the builtin of that name (eukhe, dark, light:
#    crates/eukhe-theme palette.rs BUILTIN_THEME_NAMES), else the first
#    custom file that advertises it, else the default theme eukhe with a
#    warning; the empty name picks eukhe quietly. A name that picks no
#    theme warns with the first file that did not load and advertises it
#    (or, no theme object, is named after it); every other file that did
#    not load warns once; a valid file whose name an earlier valid file has
#    clashes with the first of them. Laws (laws/theme_pick.bend):
#    theme_pick_registered, theme_pick_builtin, theme_pick_custom,
#    theme_pick_default, theme_pick_cause_first, theme_pick_cause_none,
#    theme_pick_broken_once, theme_pick_clashes_first; the resolver alone:
#    theme_resolve_first, theme_resolve_missing, theme_hit_found,
#    theme_hit_witness (anchors theme_pick_example, theme_prefix_example,
#    theme_builtin_before_custom_example).
# R6 the compiled entry: see section "The compiled entry" below. Laws:
#    theme_ffi_answers, theme_ffi_left_over, theme_ffi_unknown_tag, and
#    laws/theme_entry.bend theme_ffi_spelled and theme_ffi_refuses (anchor
#    theme_ffi_example).
# A1 Rust decodes the JSON (serde) and projects it losslessly: keys in
#    order, each string with the index of the variable it names, numbers
#    and other values as JSON writes them (the projection is glue the
#    Rust tests check, the laws cannot see it).
# T3 (section tui_color below) every color role of the terminal UI
#    resolves in the palette of every valid theme file: tui_roles_resolve.
#
# Every input is free: any registered, builtin and custom candidates in
# any order, valid or not; any name; any theme file (any colors,
# variables and export page). The shipped themes are the tables of
# bend/theme/bundled.bend; a Rust test (crates/eukhe-core, theme_rules)
# checks that the bundled files crates/eukhe-theme/themes/*.json paint
# them. Trusted (called by the specs): Co.hex, Co.num, Co.ansi256,
# Co.light, Co.contrast_ge, Co.to256 (laws/color), TToken.get (laws
# theme_model), TChase.chase in the premises of the reading laws (pinned
# by theme_chase_chain).

import Base
import ../bend/color.bend as Co
import ../bend/wire.bend as Wr
import ../bend/theme/bundled.bend as TBundled
import ../bend/theme/chase.bend as TChase
import ../bend/theme/file.bend as TFile
import ../bend/theme/palette.bend as TPalette
import ../bend/theme/reader.bend as TReader
import ../bend/theme/token.bend as TToken
import ../bend/tui_color.bend as TC
import ../bend/ffi_theme.bend as FTh
import ./base.bend as LawsBase
import ../spec/theme/wire.bend as Tw
import ../spec/theme/read.bend as Tr
import ../spec/theme/rules.bend as Ts

# ---- themes ----

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

# LAW theme_shipped_legible: in every shipped theme, every pair of the legibility test
# (TBundled.pairs: theme_pairs_cover, theme_legible_sound) meets its WCAG
# contrast: text 4.5:1, non-text parts 3:1, as exact rationals
law theme_shipped_legible:
  for s: TBundled.Shipped
  {TBundled.legible(TBundled.table(s)) == True{} : Bool}

# LAW theme_shipped_status_distinct: in every shipped theme, the status colors (accent, success,
# warning, error) stay pairwise distinct in a 256-color terminal (the
# test's meaning: theme_status_sound)
law theme_shipped_status_distinct:
  for s: TBundled.Shipped
  {TBundled.status_distinct(TBundled.table(s)) == True{} : Bool}

# Terms
# -----

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

# Values (R1, R2)

# s names a variable: it is not empty and does not start with #
def th.refers(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, rest}:
      Bool.not(Char.is_eq(c, '#'))

def th.lit.of(empty: Bool, +s: String) -> TChase.Got:
  match empty:
    case True{}:
      TChase.Hit{TFile.Dflt{}}
    case False{}:
      th.hex(Co.hex(s), s)

# a string that names no variable: "" is the terminal default, a #-string
# a #rrggbb color (Co.hex) or "Invalid hex color"
def th.lit(+s: String) -> TChase.Got:
  th.lit.of(String.is_empty(s), s)

def th.last.at(looped: Bool, m: Maybe<&2, TFile.Json>, s: String) -> Maybe<&2, TChase.Got>:
  match looped:
    case True{}:
      Some{TChase.Miss{TFile.Circular{s}}}
    case False{}:
      match m:
        case None{}:
          Some{TChase.Miss{TFile.NotFound{s}}}
        case Some{j}:
          None{}

def th.last.ref(+vars: List<&2, TFile.Var>, +met: List<&2, Nat>, s: String, at: Maybe<&2, Nat>) -> Maybe<&2, TChase.Got>:
  match at:
    case None{}:
      Some{TChase.Miss{TFile.NotFound{s}}}
    case Some{+i}:
      th.last.at(th.mem(met, i), th.var(vars, i), s)

def th.last.str(r: Bool, +vars: List<&2, TFile.Var>, +met: List<&2, Nat>, +s: String, at: Maybe<&2, Nat>) -> Maybe<&2, TChase.Got>:
  match r:
    case True{}:
      th.last.ref(vars, met, s, at)
    case False{}:
      Some{th.lit(s)}

# what the value j at the end of a chain decides, the chain having met the
# variables met: a string that names no variable or a number decides by
# itself (R1); anything else is "Invalid color value"; a reference decides
# when it names no variable (not found) or one the chain met (circular,
# named by this reference: R2); else the chain goes on (None)
def th.last(+vars: List<&2, TFile.Var>, +met: List<&2, Nat>, j: TFile.Json) -> Maybe<&2, TChase.Got>:
  match j:
    case TFile.JStr{+s, at}:
      th.last.str(th.refers(s), vars, met, s, at)
    case TFile.JNum{+t}:
      Some{th.num(Co.num(t), t)}
    case TFile.JOther{t}:
      Some{TChase.Miss{TFile.BadValue{t}}}

def th.next.at(same: Bool, +vars: List<&2, TFile.Var>, +i: Nat) -> Maybe<&2, TFile.Json>:
  match same:
    case True{}:
      th.var(vars, i)
    case False{}:
      None{}

def th.next.str(r: Bool, +vars: List<&2, TFile.Var>, at: Maybe<&2, Nat>, +i: Nat) -> Maybe<&2, TFile.Json>:
  match r:
    case True{}:
      match at:
        case None{}:
          None{}
        case Some{k}:
          th.next.at(Nat.is_eq(k, i), vars, i)
    case False{}:
      None{}

# the value of variable i, when j is a reference to it
def th.next(+vars: List<&2, TFile.Var>, j: TFile.Json, +i: Nat) -> Maybe<&2, TFile.Json>:
  match j:
    case TFile.JStr{s, at}:
      th.next.str(th.refers(s), vars, at, i)
    case TFile.JNum{t}:
      None{}
    case TFile.JOther{t}:
      None{}

def th.chain.if(m: Maybe<&2, TFile.Json>, r: Maybe<&2, TChase.Got>) -> Maybe<&2, TChase.Got>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      r

def th.or.json(m: Maybe<&2, TFile.Json>) -> TFile.Json:
  match m:
    case None{}:
      TFile.JOther{""}
    case Some{v}:
      v

# the decision at the end of the chain from j through the variables p, in
# order (each value but the last a reference to the next variable of p),
# met holding the variables met before; None when j is no such chain or
# its end does not decide
def th.chain(p: List<&2, Nat>, +vars: List<&2, TFile.Var>, met: List<&2, Nat>, +j: TFile.Json) -> Maybe<&2, TChase.Got>:
  match p:
    case Nil{}:
      th.last(vars, met, j)
    case Con{+i, rest}:
      +m = th.next(vars, j, i)
      th.chain.if(m, th.chain(rest, vars, i <> met, th.or.json(m)))

# no variable of p is met twice, met holding the variables met before
def th.fresh(p: List<&2, Nat>, +met: List<&2, Nat>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{+i, rest}:
      Bool.and(Bool.not(th.mem(met, i)), th.fresh(rest, i <> met))

# Reading a file (R3)

def th.miss(k: String, g: TChase.Got) -> Maybe<&2, TFile.Fault>:
  match g:
    case TChase.Hit{v}:
      None{}
    case TChase.Miss{why}:
      Some{TFile.InColor{k, why}}

# the fault a color entry reports: a key that names no token is unknown; a
# value that resolves to no color is that value's error, under its key;
# none when the entry reads
def th.fault(+vars: List<&2, TFile.Var>, e: TFile.REnt) -> Maybe<&2, TFile.Fault>:
  match e:
    case TFile.REnt{k, t, j}:
      match t:
        case None{}:
          Some{TFile.Unknown{k}}
        case Some{x}:
          th.miss(k, TChase.chase(vars, j))

def th.none(m: Maybe<&2, TFile.Fault>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

# every entry of es reads
def th.clean(+vars: List<&2, TFile.Var>, es: List<&2, TFile.REnt>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, rest}:
      Bool.and(th.none(th.fault(vars, e)), th.clean(vars, rest))

def th.ent.got(t: U32, g: TChase.Got) -> TFile.Ent:
  match g:
    case TChase.Hit{v}:
      TFile.Ent{t, v}
    case TChase.Miss{why}:
      TFile.Ent{0, TFile.Dflt{}}

# the color an entry that reads gives: its token, its value resolved
def th.ent(+vars: List<&2, TFile.Var>, e: TFile.REnt) -> TFile.Ent:
  match e:
    case TFile.REnt{k, t, j}:
      match t:
        case None{}:
          TFile.Ent{0, TFile.Dflt{}}
        case Some{x}:
          th.ent.got(x, TChase.chase(vars, j))

# the entries es read (when every one reads)
def th.goods(+vars: List<&2, TFile.Var>, es: List<&2, TFile.REnt>) -> List<&2, TFile.Ent>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, rest}:
      th.ent(vars, e) <> th.goods(vars, rest)

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

# Completion (R4)

def th.vals(p: TPalette.Parsed) -> List<&2, TFile.Val>:
  match p:
    case TPalette.Rejected{x}:
      []
    case TPalette.Painted{vs, l, d, pg, cd, io}:
      vs

# the value a parsed file gives token k (its k-th value, from 0)
def th.tok(p: TPalette.Parsed, k: Nat) -> Maybe<&2, TFile.Val>:
  List.get(&2, TFile.Val, th.vals(p), k)

def th.light(p: TPalette.Parsed) -> Bool:
  match p:
    case TPalette.Rejected{x}:
      False{}
    case TPalette.Painted{vs, l, d, pg, cd, io}:
      l

def th.declared(p: TPalette.Parsed) -> Maybe<&2, Co.Rgb>:
  match p:
    case TPalette.Rejected{x}:
      None{}
    case TPalette.Painted{vs, l, d, pg, cd, io}:
      d

def th.exports(p: TPalette.Parsed) -> List<&2, Maybe<&2, Co.Rgb>>:
  match p:
    case TPalette.Rejected{x}:
      []
    case TPalette.Painted{vs, l, d, pg, cd, io}:
      [pg, cd, io]

# the builtin a mode's optional tokens come from: light for a light
# background, the default theme eukhe for a dark one (crates/eukhe-theme
# palette.rs DEFAULT_THEME_NAME, LIGHT_THEME_NAME)
def th.builtin.of(light: Bool) -> TBundled.Shipped:
  match light:
    case True{}:
      TBundled.Light{}
    case False{}:
      TBundled.Eukhe{}

def th.hexs(m: Maybe<&2, Co.Rgb>) -> Maybe<&2, TFile.Val>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      Some{TFile.Hex{c}}

# token k of the builtin of a mode, as a written color
def th.builtin.val(light: Bool, k: Nat) -> Maybe<&2, TFile.Val>:
  th.hexs(List.get(&2, Co.Rgb, TBundled.table(th.builtin.of(light)), k))

# the color a written value paints where the terminal is not asked: none
# for "" (the terminal default) or no value, an index's xterm-256 color, a
# #rrggbb color itself (R1)
def th.paints(m: Maybe<&2, TFile.Val>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case TFile.Dflt{}:
          None{}
        case TFile.Idx{i}:
          Some{Co.ansi256(i)}
        case TFile.Hex{c}:
          Some{c}

# a value written as #rrggbb
def th.hexed(m: Maybe<&2, TFile.Val>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      match v:
        case TFile.Dflt{}:
          False{}
        case TFile.Idx{i}:
          False{}
        case TFile.Hex{c}:
          True{}

# Shipped tables (R4)

# the legibility test's pair of a token: its surface and the contrast it
# needs, by its role in crates/eukhe-theme token.rs (Token::ALL order):
# 48..57 are surfaces (the *Bg tokens and background) and the lift ends 45,
# 46 paint no ink (a selection band moves toward them): no pair; the
# non-text parts (border 1, borderAccent 2, borderMuted 3,
# mdCodeBlockBorder 24, mdQuoteBorder 26, mdHr 27, effortLow 42,
# effortHigh 43, bashMode 47) on the background at 3:1 (WCAG 2.x SC
# 1.4.11); every other token is text, at 4.5:1 (SC 1.4.3), on the
# background, but userMessageText 11 and customMessageText 12 on their own
# surfaces userMessageBg 49 and customMessageBg 50
def th.part(t: Nat) -> Bool:
  th.mem([1n, 2n, 3n, 24n, 26n, 27n, 42n, 43n, 47n], t)

def th.ground.of(user: Bool, custom: Bool) -> Nat:
  match user:
    case True{}:
      49n
    case False{}:
      match custom:
        case True{}:
          50n
        case False{}:
          57n

def th.ground(+t: Nat) -> Nat:
  th.ground.of(Nat.is_eq(t, 11n), Nat.is_eq(t, 12n))

def th.need.of(none: Bool, part: Bool, +t: Nat) -> Maybe<&2, TBundled.Duo>:
  match none:
    case True{}:
      None{}
    case False{}:
      match part:
        case True{}:
          Some{TBundled.Duo{t, 57n, 3, 1}}
        case False{}:
          Some{TBundled.Duo{t, th.ground(t), 9, 2}}

def th.need(+t: Nat) -> Maybe<&2, TBundled.Duo>:
  th.need.of(Bool.or(Bool.and(Nat.is_le(48n, t), Nat.is_le(t, 57n)), Bool.or(Nat.is_eq(t, 45n), Nat.is_eq(t, 46n))), th.part(t), t)

def th.duo.eq(a: TBundled.Duo, b: TBundled.Duo) -> Bool:
  match a b:
    case TBundled.Duo{f1, g1, n1, d1} TBundled.Duo{f2, g2, n2, d2}:
      Bool.and(Nat.is_eq(f1, f2), Bool.and(Nat.is_eq(g1, g2), Bool.and(U32.is_eq(n1, n2), U32.is_eq(d1, d2))))

def th.duo.in(ps: List<&2, TBundled.Duo>, +d: TBundled.Duo) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{p, rest}:
      Bool.or(th.duo.eq(p, d), th.duo.in(rest, d))

def th.covers(m: Maybe<&2, TBundled.Duo>, +ps: List<&2, TBundled.Duo>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{d}:
      th.duo.in(ps, d)

# every token from t on (n of them) has its pair in ps
def th.covered(n: Nat, +t: Nat, +ps: List<&2, TBundled.Duo>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+k:
      Bool.and(th.covers(th.need(t), ps), th.covered(k, 1n+t, ps))

# the 256-color terminal paints tokens a and b of the table xs apart
def th.apart(+xs: List<&2, Co.Rgb>, a: Nat, b: Nat) -> Bool:
  Bool.not(U32.is_eq(Co.to256(Ts.get(xs, a)), Co.to256(Ts.get(xs, b))))

# Laws
# ----

# Values

# LAW theme_chase_chain (R1, R2): a value resolves at the end of its chain of references: when
# j, followed through the variables p (each value but the last a
# reference, a non-empty string not starting with #, to the next variable
# of p), ends in a value that decides (a color or a malformed value, R1; a
# reference to no variable: not found; a reference to a variable of p: a
# cycle named by that reference, R2), j resolves to that decision, for
# every variables. Premises: no variable of p repeats (so p is no longer
# than the variables: stated, not derived)
# EXCLUDES: a chain followed too far or not far enough, a cycle or a
#   missing variable reported as another error or with another name (the
#   start of the chain), a malformed color read as a default, a lookup
#   tree that answers another variable
law theme_chase_chain:
  for +vars: List<&2, TFile.Var>
  for +j: TFile.Json
  for +p: List<&2, Nat>
  for +g: TChase.Got
  for d: {th.fresh(p, []) == True{} : Bool}
  for n: {Nat.is_le(List.length(&2, Nat, p), List.length(&2, TFile.Var, vars)) == True{} : Bool}
  for e: {th.chain(p, vars, [], j) == Some{g} : Maybe<&2, TChase.Got>}
  {TChase.chase(vars, j) == g : TChase.Got}

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

# LAW theme_read_first_error (R3): a file whose colors before e all read (th.clean) and whose
# entry e reports the fault f (th.fault: its key names no token, or its
# value resolves to no color, under its key) is rejected with f, whatever
# follows
# EXCLUDES: reporting a later error first, a missing token before a
#   color error, skipping an unknown key, an error that loses its key or
#   its cause, a palette for a broken file
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
  for bad: {th.fault(vars, e) == Some{f} : Maybe<&2, TFile.Fault>}
  {TPalette.parse(TFile.RFile{nm, vars, List.append(&2, TFile.REnt, pre, e <> post), pg, cd, io}) == TPalette.Rejected{f} : TPalette.Parsed}

# LAW theme_required_tokens (R3): the model's required tokens are the documented ones
# EXCLUDES: a token made optional or required by mistake
law theme_required_tokens:
  {th.reqs(TToken.toks()) == th.required() : List<&2, U32>}

# LAW theme_read_missing (R3): a file whose colors read is rejected with every required token it
# does not write, in token order
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
  {TPalette.parse(TFile.RFile{nm, vars, cols, pg, cd, io}) == TPalette.Rejected{TFile.Missing{t <> ts}} : TPalette.Parsed}

# LAW theme_read_page (R3): then an export page that is no color rejects the file with that
# error
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
  {TPalette.parse(TFile.RFile{nm, vars, cols, Some{j}, cd, io}) == TPalette.Rejected{TFile.InExport{TFile.OnPage{}, why}} : TPalette.Parsed}

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
  {TPalette.parse(TFile.RFile{nm, vars, cols, pg, Some{j}, io}) == TPalette.Rejected{TFile.InExport{TFile.OnCard{}, why}} : TPalette.Parsed}

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
  {TPalette.parse(TFile.RFile{nm, vars, cols, pg, cd, Some{j}}) == TPalette.Rejected{TFile.InExport{TFile.OnInfo{}, why}} : TPalette.Parsed}

# LAW theme_read_loaded (R3): R4 a file with no error reads to its colors (each entry's token
# and resolved value, th.goods, in key order) and the export colors it sets
# ("" sets none)
# EXCLUDES: dropping or reordering a color, a color stored under another
#   token or with another value, losing the card or info background, an
#   export "" that sets a color
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
# Each law below is about the parse (TPalette.parse, what the entry
# answers) of a file f that reads to colors cols and export backgrounds
# pg, cd, io (theme_read_loaded); none depends on the file's name.

# LAW theme_parse_tokens (R4): a file that reads paints one value per token: 59 (crates/eukhe-theme
# Token::ALL)
# EXCLUDES: a palette that skips, doubles or adds a token
law theme_parse_tokens:
  for +f: TFile.RFile
  for +nm: String
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  for h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}
  {List.length(&2, TFile.Val, th.vals(TPalette.parse(f))) == 59n : Nat}

# LAW theme_parse_written (R4): every token but background (57) and foreground (58) that the
# file writes keeps the value written (its first entry), at its place in
# token order
# EXCLUDES: a written color replaced by a default or by another token's,
#   a palette in another order, text overriding a written mdBody, a
#   builtin over a written refinement color
law theme_parse_written:
  for +f: TFile.RFile
  for +nm: String
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  for +i: Nat
  for +v: TFile.Val
  for h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}
  for lt: {Nat.is_lt(i, 57n) == True{} : Bool}
  for w: {TToken.get(cols, U32.from_nat(i)) == Some{v} : Maybe<&2, TFile.Val>}
  {th.tok(TPalette.parse(f), i) == Some{v} : Maybe<&2, TFile.Val>}

# LAW theme_parse_md (R4): an mdBody (18) the file does not write paints as text (9)
# EXCLUDES: mdBody without a fallback, or with another token's value
law theme_parse_md:
  for +f: TFile.RFile
  for +nm: String
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  for h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}
  for u: {TToken.get(cols, 18) == None{} : Maybe<&2, TFile.Val>}
  {th.tok(TPalette.parse(f), 18n) == th.tok(TPalette.parse(f), 9n) : Maybe<&2, TFile.Val>}

# LAW theme_parse_refinement (R4): a refinementHeader (14) or refinementSummary (15) the file does
# not write paints as that token of the builtin of the file's mode (light
# when the parse says light, else the default theme eukhe)
# EXCLUDES: a dark default on a light theme, a terminal default left in
#   the pair, the other token's builtin color
law theme_parse_refinement:
  for +f: TFile.RFile
  for +nm: String
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  for h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}
  ({TToken.get(cols, 14) == None{} : Maybe<&2, TFile.Val>} -> {th.tok(TPalette.parse(f), 14n) == th.builtin.val(th.light(TPalette.parse(f)), 14n) : Maybe<&2, TFile.Val>}) & ({TToken.get(cols, 15) == None{} : Maybe<&2, TFile.Val>} -> {th.tok(TPalette.parse(f), 15n) == th.builtin.val(th.light(TPalette.parse(f)), 15n) : Maybe<&2, TFile.Val>})

# LAW theme_parse_foreground (R4): the foreground (58) paints as a #rrggbb color: the one its
# written value paints (an index's xterm-256 color), else (unset or "")
# that token of the builtin of the file's mode
# EXCLUDES: a terminal default or an index left in the foreground, a
#   default over a written color, a dark default on a light theme
law theme_parse_foreground:
  for +f: TFile.RFile
  for +nm: String
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  for +c: Co.Rgb
  for h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}
  ({th.paints(TToken.get(cols, 58)) == Some{c} : Maybe<&2, Co.Rgb>} -> {th.tok(TPalette.parse(f), 58n) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>}) & ({th.paints(TToken.get(cols, 58)) == None{} : Maybe<&2, Co.Rgb>} -> {th.tok(TPalette.parse(f), 58n) == th.builtin.val(th.light(TPalette.parse(f)), 58n) : Maybe<&2, TFile.Val>})

# LAW theme_parse_background (R4): the background (57) paints as a #rrggbb color: the one the
# file's own background paints, else its export page, else the one its
# user-message surface (49) paints, else the default theme's background
# EXCLUDES: another order of the fallbacks, a default over a written
#   color, a terminal default or an index left in the background
law theme_parse_background:
  for +f: TFile.RFile
  for +nm: String
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  for +c: Co.Rgb
  for h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}
  ({th.paints(TToken.get(cols, 57)) == Some{c} : Maybe<&2, Co.Rgb>} -> {th.tok(TPalette.parse(f), 57n) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>}) & ({th.paints(TToken.get(cols, 57)) == None{} : Maybe<&2, Co.Rgb>} -> {pg == Some{c} : Maybe<&2, Co.Rgb>} -> {th.tok(TPalette.parse(f), 57n) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>}) & ({th.paints(TToken.get(cols, 57)) == None{} : Maybe<&2, Co.Rgb>} -> {pg == None{} : Maybe<&2, Co.Rgb>} -> {th.paints(TToken.get(cols, 49)) == Some{c} : Maybe<&2, Co.Rgb>} -> {th.tok(TPalette.parse(f), 57n) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>}) & ({th.paints(TToken.get(cols, 57)) == None{} : Maybe<&2, Co.Rgb>} -> {pg == None{} : Maybe<&2, Co.Rgb>} -> {th.paints(TToken.get(cols, 49)) == None{} : Maybe<&2, Co.Rgb>} -> {th.tok(TPalette.parse(f), 57n) == th.builtin.val(False{}, 57n) : Maybe<&2, TFile.Val>})

# LAW theme_parse_mode (R4): the file is light exactly when the background it paints is light
# (Co.light: WCAG relative luminance above one half)
# EXCLUDES: a constant mode, a mode from another color than the painted
#   background
law theme_parse_mode:
  for +f: TFile.RFile
  for +nm: String
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  for +c: Co.Rgb
  for h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}
  for b: {th.tok(TPalette.parse(f), 57n) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>}
  {th.light(TPalette.parse(f)) == Co.light(c) : Bool}

# LAW theme_parse_declared (R4): the parse reports the file's own background exactly when the file
# writes it as #rrggbb (the terminal UI's onboarding canvas), and the
# export page, card and info backgrounds the file reads to
# EXCLUDES: a declared background from an index, "" or the fallbacks, a
#   lost or swapped export background
law theme_parse_declared:
  for +f: TFile.RFile
  for +nm: String
  for +cols: List<&2, TFile.Ent>
  for +pg: Maybe<&2, Co.Rgb>
  for +cd: Maybe<&2, Co.Rgb>
  for +io: Maybe<&2, Co.Rgb>
  for +c: Co.Rgb
  for h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}
  ({TToken.get(cols, 57) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>} -> {th.declared(TPalette.parse(f)) == Some{c} : Maybe<&2, Co.Rgb>}) & ({th.hexed(TToken.get(cols, 57)) == False{} : Bool} -> {th.declared(TPalette.parse(f)) == None{} : Maybe<&2, Co.Rgb>}) & {th.exports(TPalette.parse(f)) == [pg, cd, io] : List<&2, Maybe<&2, Co.Rgb>>}

# LAW theme_light_example (R4): anchor: a file with a white background is light, one with a
# black background dark
# EXCLUDES: a constant mode
law theme_light_example:
  {[TPalette.light(TFile.Th{"w", [TFile.Ent{57, TFile.Hex{Co.Rgb{255, 255, 255}}}], None{}, None{}, None{}}), TPalette.light(TFile.Th{"b", [TFile.Ent{57, TFile.Hex{Co.Rgb{0, 0, 0}}}], None{}, None{}, None{}})] == [True{}, False{}] : List<&2, Bool>}

# Shipped tables

# LAW theme_legible_sound (R4): a table passes the legibility test only when every pair of the
# test meets its contrast: the WCAG ratio of the pair's two tokens (black
# past the table's end) is at least num/den (Co.contrast_ge), for every
# table and every pair of TBundled.pairs
# EXCLUDES: a constant or partial legibility test (theme_shipped_legible
#   made vacuous), a pair checked on other tokens or another need
law theme_legible_sound:
  for +xs: List<&2, Co.Rgb>
  for +pre: List<&2, TBundled.Duo>
  for +fg: Nat
  for +bg: Nat
  for +num: U32
  for +den: U32
  for +post: List<&2, TBundled.Duo>
  for at: {TBundled.pairs() == List.append(&2, TBundled.Duo, pre, TBundled.Duo{fg, bg, num, den} <> post) : List<&2, TBundled.Duo>}
  for ok: {TBundled.legible(xs) == True{} : Bool}
  {Co.contrast_ge(Ts.get(xs, fg), Ts.get(xs, bg), num, den) == True{} : Bool}

# LAW theme_pairs_cover (R4): the legibility test checks every ink token of the 59 (th.need: text
# at 4.5:1 on its surface, a non-text part at 3:1 on the background)
# EXCLUDES: a dropped or weakened pair (an ink token never checked)
law theme_pairs_cover:
  {th.covered(59n, 0n, TBundled.pairs()) == True{} : Bool}

# LAW theme_status_sound (R4): a table passes the status test only when its status colors accent
# (0), success (4), warning (6) and error (5) (crates/eukhe-theme
# Token::ALL) are pairwise different 256-color indices (Co.to256), for
# every table
# EXCLUDES: a constant status test (theme_shipped_status_distinct made
#   vacuous), other tokens compared, a pair left out
law theme_status_sound:
  for +xs: List<&2, Co.Rgb>
  for ok: {TBundled.status_distinct(xs) == True{} : Bool}
  {[th.apart(xs, 0n, 4n), th.apart(xs, 0n, 6n), th.apart(xs, 0n, 5n), th.apart(xs, 4n, 6n), th.apart(xs, 4n, 5n), th.apart(xs, 6n, 5n)] == [True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}

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

# LAW theme_ffi_left_over (R6): a request followed by more input is refused whole
# EXCLUDES: an entry that answers a prefix of its input and drops the rest
law theme_ffi_left_over:
  for +r: FTh.Req
  for fits: {Tw.fits(r) == True{} : Bool}
  for c: Char
  for x: String
  {FTh.ffi(Tw.req(r, SCon{c, x})) == Tr.refused() : String}

# LAW theme_ffi_unknown_tag (R6): an input whose first number (the request's tag, within the
# wire) is 3 or more, no request kind (0 load, 1 resolve, 2 shipped), is
# refused, whatever follows
# EXCLUDES: an unknown tag read as a known request (a default load, a
#   guessed theme), a partial reply
law theme_ffi_unknown_tag:
  for +k: Nat
  for +rest: String
  for big: {Nat.is_le(3n, k) == True{} : Bool}
  for fits: {LawsBase.wire_fits(k) == True{} : Bool}
  {FTh.ffi(Wr.put_nat(k, rest)) == Tr.refused() : String}

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
# The model in bend/tui_color.bend:
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

# eukhe: the laws of area theme_pick: the theme a name picks
#
# LAWS (T1, R5 of laws/theme.bend): each law is an open claim about the
# resolver of bend/theme/name.bend or the pick of bend/theme/choice.bend
# (what the entry bend/ffi_theme.bend answers for a resolve); PROOF.bend
# proves them (as ThemePick.<law>) with the lemmas of proof/theme_pick/.
#
# Requirements (laws/theme.bend header; crates/eukhe-theme sources.rs,
# palette.rs; the requirement resolves the builtins, then the custom
# directory):
# R5 a name picks, among the files that load: the first registered file
#    that advertises it (theme_pick_registered), else the builtin of that
#    name, eukhe 0, dark 1, light 2 (palette.rs BUILTIN_THEME_NAMES;
#    theme_pick_builtin), else the first custom file that advertises it
#    (theme_pick_custom), else the default theme eukhe with a warning; the
#    empty name picks eukhe quietly (theme_pick_default). A name that picks
#    no theme warns with the first file that did not load and advertises
#    it (or, no theme object, is named after it), else "no theme"
#    (theme_pick_cause_first, theme_pick_cause_none); every other file
#    that did not load warns once (theme_pick_broken_once); a valid file
#    whose name an earlier valid file has clashes with the first of them
#    (theme_pick_clashes_first). The resolver over candidates:
#    theme_resolve_first, theme_resolve_missing, with hit pinned by
#    theme_hit_found and theme_hit_witness. Anchors: theme_pick_example,
#    theme_prefix_example, theme_builtin_before_custom_example.

import Base
import ../bend/theme/choice.bend as TChoice
import ../bend/theme/name.bend as TName
import ../bend/ffi_theme.bend as FTh

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

# a valid candidate named n splits src: the candidates before it, its
# name and id, the candidates after it
def th.HitAt(src: List<&2, TName.Cand>, n: String) -> Type:
  &pre: List<&2, TName.Cand> -> &nm: String -> &id: U32 -> &post: List<&2, TName.Cand> -> ({src == List.append(&2, TName.Cand, pre, TName.Cand{nm, True{}, id} <> post) : List<&2, TName.Cand>} & {String.eq(nm, n) == True{} : Bool})

# LAW theme_hit_found (R5): a valid candidate whose name is exactly n, anywhere among the
# candidates, makes hit(src, n) true (so hit(src, n) false, the premise of
# theme_resolve_first and theme_resolve_missing, means no valid candidate
# of src advertises n)
# EXCLUDES: a valid candidate missed (resolve laws claimed for names that
#   resolve), a scan that stops early
law theme_hit_found:
  for +pre: List<&2, TName.Cand>
  for +nm: String
  for +id: U32
  for +post: List<&2, TName.Cand>
  for +n: String
  for same: {String.eq(nm, n) == True{} : Bool}
  {TName.hit(List.append(&2, TName.Cand, pre, TName.Cand{nm, True{}, id} <> post), n) == True{} : Bool}

# LAW theme_hit_witness (R5): hit(src, n) is true only when src holds a valid candidate whose
# name is exactly n: src splits around it
# EXCLUDES: a hit for an invalid candidate, a prefix, case-folded or
#   substring match, a constant hit (theme_resolve_first and
#   theme_resolve_missing made vacuous)
law theme_hit_witness:
  for +src: List<&2, TName.Cand>
  for +n: String
  for h: {TName.hit(src, n) == True{} : Bool}
  th.HitAt(src, n)

# Terms
# -----

# x is in xs
def th.mem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(Nat.is_eq(y, x), th.mem(rest, x))

# Picking a theme (R5)

# l loaded and advertises exactly the name n, from the registered sources
def th.offers.reg(l: TChoice.Ld, +n: String) -> Bool:
  match l:
    case TChoice.Fine{nm, c}:
      match c:
        case True{}:
          False{}
        case False{}:
          String.eq(nm, n)
    case TChoice.Broke{nm, st}:
      False{}

# l loaded and advertises exactly the name n, from the custom directory
def th.offers.custom(l: TChoice.Ld, +n: String) -> Bool:
  match l:
    case TChoice.Fine{nm, c}:
      match c:
        case True{}:
          String.eq(nm, n)
        case False{}:
          False{}
    case TChoice.Broke{nm, st}:
      False{}

# no file of ls offers n from the registered sources
def th.none.reg(ls: List<&2, TChoice.Ld>, +n: String) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, rest}:
      Bool.and(Bool.not(th.offers.reg(l, n)), th.none.reg(rest, n))

# no file of ls offers n from the custom directory
def th.none.custom(ls: List<&2, TChoice.Ld>, +n: String) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, rest}:
      Bool.and(Bool.not(th.offers.custom(l, n)), th.none.custom(rest, n))

# the builtin themes, in the order of crates/eukhe-theme palette.rs
# BUILTIN_THEME_NAMES (their ids 0, 1, 2): eukhe (the default theme: the
# one an empty name and every failed lookup resolve to), dark, light
def th.builtin.names() -> List<&2, String>:
  ["eukhe", "dark", "light"]

def th.index.if(hit: Bool, at: Nat, other: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{at}
    case False{}:
      other

def th.index(xs: List<&2, String>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, rest}:
      th.index.if(String.eq(x, n), at, th.index(rest, n, 1n+at))

# the id of the builtin named n
def th.builtin(+n: String) -> Maybe<&2, Nat>:
  th.index(th.builtin.names(), n, 0n)

# a file that did not load blames name n: it advertises n, or it is no
# theme object and its stem is n
def th.same(m: Maybe<&2, String>, +n: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      String.eq(x, n)

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

# no file of ls blames n
def th.none.blame(ls: List<&2, TChoice.Ld>, +n: String) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, rest}:
      Bool.and(Bool.not(th.blames(l, n)), th.none.blame(rest, n))

def th.res(p: TChoice.Pick) -> TName.Res:
  match p:
    case TChoice.Pick{r, c, k, b}:
      r

def th.warned(p: TChoice.Pick) -> Bool:
  match p:
    case TChoice.Pick{r, c, k, b}:
      match r:
        case TName.Res{id, w}:
          w

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

# Some{c} when the pick warns, else none
def th.when(w: Bool, c: TChoice.Cause) -> Maybe<&2, TChoice.Cause>:
  match w:
    case True{}:
      Some{c}
    case False{}:
      None{}

def th.broke.of(m: Maybe<&2, TChoice.Ld>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{l}:
      match l:
        case TChoice.Fine{nm, c}:
          False{}
        case TChoice.Broke{nm, st}:
          True{}

# the file at index i did not load
def th.broke.at(ls: List<&2, TChoice.Ld>, i: Nat) -> Bool:
  th.broke.of(List.get(&2, TChoice.Ld, ls, i))

# the cause is the file at index i
def th.cause.at(m: Maybe<&2, TChoice.Cause>, +i: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      match c:
        case TChoice.FailedAt{k}:
          Nat.is_eq(k, i)
        case TChoice.NoTheme{}:
          False{}

def th.above(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Nat.is_lt(x, y)

# every number of xs is below the next one
def th.rising(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(th.above(rest, x), th.rising(rest))

def th.name.of(m: Maybe<&2, TChoice.Ld>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{l}:
      match l:
        case TChoice.Fine{nm, c}:
          Some{nm}
        case TChoice.Broke{nm, st}:
          None{}

# the name of the file at index i, when it loaded
def th.name.at(ls: List<&2, TChoice.Ld>, i: Nat) -> Maybe<&2, String>:
  th.name.of(List.get(&2, TChoice.Ld, ls, i))

# no file of ls loaded with the name n
def th.unnamed(ls: List<&2, TChoice.Ld>, +n: String) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, rest}:
      match l:
        case TChoice.Fine{nm, c}:
          Bool.and(Bool.not(String.eq(nm, n)), th.unnamed(rest, n))
        case TChoice.Broke{nm, st}:
          th.unnamed(rest, n)

def th.clash.name(m: Maybe<&2, String>, +ls: List<&2, TChoice.Ld>, +i: Nat, +w: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+n}:
      Bool.and(Bool.not(Nat.is_eq(w, i)), Bool.and(th.same(th.name.at(ls, w), n), th.unnamed(List.take(&2, TChoice.Ld, ls, w), n)))

# the file at index i clashes with the one at w: both loaded with the same
# name, no file before w loaded with that name (w is the first of them),
# and w is not i (so w comes before i)
def th.clash.ok(+ls: List<&2, TChoice.Ld>, +i: Nat, +w: Nat) -> Bool:
  th.clash.name(th.name.at(ls, i), ls, i, w)

# Clash{i, w} is in cs
def th.clash.in(cs: List<&2, TChoice.Clash>, +i: Nat, +w: Nat) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, rest}:
      match c:
        case TChoice.Clash{a, b}:
          Bool.or(Bool.and(Nat.is_eq(a, i), Nat.is_eq(b, w)), th.clash.in(rest, i, w))

def th.clash.above(cs: List<&2, TChoice.Clash>, +x: Nat) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      match c:
        case TChoice.Clash{a, b}:
          Nat.is_lt(x, a)

# every clash's file is below the next clash's
def th.clash.rising(cs: List<&2, TChoice.Clash>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, +rest}:
      match c:
        case TChoice.Clash{+a, b}:
          Bool.and(th.clash.above(rest, a), th.clash.rising(rest))

# Picking a theme
# Each law below is about TChoice.pick(ls, n): the files ls the sources
# reach (registered and custom, in order), the file at index i the
# candidate 3 + i (the builtins are 0 eukhe, 1 dark, 2 light).

# LAW theme_pick_registered (R5): a name picks the first registered file that loaded and
# advertises it (3 + its index), with no warning: before every builtin
# and every custom file
# EXCLUDES: a builtin or custom file before a registered one, a later
#   registered file, a file that did not load, an id off its index
law theme_pick_registered:
  for +pre: List<&2, TChoice.Ld>
  for +nm: String
  for +post: List<&2, TChoice.Ld>
  for +n: String
  for ne: {String.is_empty(n) == False{} : Bool}
  for no: {th.none.reg(pre, n) == True{} : Bool}
  for same: {String.eq(nm, n) == True{} : Bool}
  {th.res(TChoice.pick(List.append(&2, TChoice.Ld, pre, TChoice.Fine{nm, False{}} <> post), n)) == TName.Res{U32.from_nat(Nat.add(3n, List.length(&2, TChoice.Ld, pre))), False{}} : TName.Res}

# LAW theme_pick_builtin (R5): a name that no registered file offers and that names a builtin
# picks that builtin (its index in BUILTIN_THEME_NAMES), with no warning,
# whatever the custom files
# EXCLUDES: a custom file shadowing a builtin, a builtin renumbered,
#   renamed or dropped
law theme_pick_builtin:
  for +ls: List<&2, TChoice.Ld>
  for +n: String
  for +k: Nat
  for no: {th.none.reg(ls, n) == True{} : Bool}
  for b: {th.builtin(n) == Some{k} : Maybe<&2, Nat>}
  {th.res(TChoice.pick(ls, n)) == TName.Res{U32.from_nat(k), False{}} : TName.Res}

# LAW theme_pick_custom (R5): a name that no registered file offers and no builtin has picks the
# first custom file that loaded and advertises it, with no warning
# EXCLUDES: a later custom file, a file that did not load, a custom file
#   ignored
law theme_pick_custom:
  for +pre: List<&2, TChoice.Ld>
  for +nm: String
  for +post: List<&2, TChoice.Ld>
  for +n: String
  for ne: {String.is_empty(n) == False{} : Bool}
  for no: {th.none.reg(List.append(&2, TChoice.Ld, pre, TChoice.Fine{nm, True{}} <> post), n) == True{} : Bool}
  for nb: {th.builtin(n) == None{} : Maybe<&2, Nat>}
  for noc: {th.none.custom(pre, n) == True{} : Bool}
  for same: {String.eq(nm, n) == True{} : Bool}
  {th.res(TChoice.pick(List.append(&2, TChoice.Ld, pre, TChoice.Fine{nm, True{}} <> post), n)) == TName.Res{U32.from_nat(Nat.add(3n, List.length(&2, TChoice.Ld, pre))), False{}} : TName.Res}

# LAW theme_pick_default (R5): the empty name picks the default theme eukhe (0) with no warning
# and no cause, whatever the files; a name that no file offers (registered
# or custom) and no builtin has picks eukhe with a warning
# EXCLUDES: another default theme, a quiet miss, a warned or failed empty
#   name
law theme_pick_default:
  for +ls: List<&2, TChoice.Ld>
  for +n: String
  ({String.is_empty(n) == True{} : Bool} -> ({th.res(TChoice.pick(ls, n)) == TName.Res{0, False{}} : TName.Res} & {th.cause(TChoice.pick(ls, n)) == None{} : Maybe<&2, TChoice.Cause>})) & ({String.is_empty(n) == False{} : Bool} -> {th.none.reg(ls, n) == True{} : Bool} -> {th.builtin(n) == None{} : Maybe<&2, Nat>} -> {th.none.custom(ls, n) == True{} : Bool} -> {th.res(TChoice.pick(ls, n)) == TName.Res{0, True{}} : TName.Res})

# LAW theme_pick_cause_first (R5): when the first file that blames the name (did not load and
# advertises it, or is no theme object named after it) is at index
# length(pre), a pick that warns has it as its cause, and a pick that does
# not warn has no cause
# EXCLUDES: a cause from a later file, a cause that is not the name's, a
#   cause reported for a quiet pick, a warning with no cause
law theme_pick_cause_first:
  for +pre: List<&2, TChoice.Ld>
  for +x: TChoice.Ld
  for +post: List<&2, TChoice.Ld>
  for +n: String
  for no: {th.none.blame(pre, n) == True{} : Bool}
  for bl: {th.blames(x, n) == True{} : Bool}
  {th.cause(TChoice.pick(List.append(&2, TChoice.Ld, pre, x <> post), n)) == th.when(th.warned(TChoice.pick(List.append(&2, TChoice.Ld, pre, x <> post), n)), TChoice.FailedAt{List.length(&2, TChoice.Ld, pre)}) : Maybe<&2, TChoice.Cause>}

# LAW theme_pick_cause_none (R5): when no file blames the name, a pick that warns has the cause
# "no theme", and a pick that does not warn has no cause
# EXCLUDES: a file blamed that does not advertise the name, a cause
#   reported for a quiet pick, a warning with no cause
law theme_pick_cause_none:
  for +ls: List<&2, TChoice.Ld>
  for +n: String
  for no: {th.none.blame(ls, n) == True{} : Bool}
  {th.cause(TChoice.pick(ls, n)) == th.when(th.warned(TChoice.pick(ls, n)), TChoice.NoTheme{}) : Maybe<&2, TChoice.Cause>}

# LAW theme_pick_broken_once (R5): every file that did not load warns exactly once: the broken
# list holds index i exactly when the file at i did not load and is not
# the cause, and it lists them in file order, each once
# EXCLUDES: a lost or doubled failure, a loaded file reported broken, the
#   cause reported twice, another order
law theme_pick_broken_once:
  for +ls: List<&2, TChoice.Ld>
  for +n: String
  for +i: Nat
  {th.mem(th.broken.of(TChoice.pick(ls, n)), i) == Bool.and(th.broke.at(ls, i), Bool.not(th.cause.at(th.cause(TChoice.pick(ls, n)), i))) : Bool} & {th.rising(th.broken.of(TChoice.pick(ls, n))) == True{} : Bool}

# LAW theme_pick_clashes_first (R5): the clashes: Clash{i, w} is reported exactly when the files at
# i and w loaded with the same name, no file before w loaded with that name
# (w is the first of them) and w is another file than i (so w < i); in
# file order, each file once
# EXCLUDES: a lost clash, a clash with the wrong file (not the first), a
#   file clashing with itself or a later one, a broken file clashing,
#   another order or a doubled clash
law theme_pick_clashes_first:
  for +ls: List<&2, TChoice.Ld>
  for +n: String
  for +i: Nat
  for +w: Nat
  {th.clash.in(th.clashes.of(TChoice.pick(ls, n)), i, w) == th.clash.ok(ls, i, w) : Bool} & {th.clash.rising(th.clashes.of(TChoice.pick(ls, n))) == True{} : Bool}

def th.ls() -> List<&2, TChoice.Ld>:
  [TChoice.Fine{"dusk", False{}}, TChoice.Broke{Some{"mist"}, Some{"a"}}, TChoice.Broke{None{}, Some{"mist"}}, TChoice.Fine{"dusk", True{}}]

# LAW theme_pick_example (R5): anchor: a registered "dusk" shadows a custom one (a clash), a
# broken file named "mist" is the cause for "mist"
# EXCLUDES: a reading of the laws above that the human did not mean
law theme_pick_example:
  {[TChoice.pick(th.ls(), "dusk"), TChoice.pick(th.ls(), "mist")] == [TChoice.Pick{TName.Res{3, False{}}, None{}, [TChoice.Clash{3n, 0n}], [1n, 2n]}, TChoice.Pick{TName.Res{0, True{}}, Some{TChoice.FailedAt{1n}}, [TChoice.Clash{3n, 0n}], [2n]}] : List<&2, TChoice.Pick>}

# LAW theme_prefix_example (R5): anchor: "d" names no theme (dark starts with it): the default
# theme, with the warning "not found"
# EXCLUDES: a name matched by prefix
law theme_prefix_example:
  {TChoice.pick([], "d") == TChoice.Pick{TName.Res{0, True{}}, Some{TChoice.NoTheme{}}, [], []} : TChoice.Pick} & {FTh.ffi("1,1,d0,") == "0,T1,1,0,0,0,0," : String}

# LAW theme_builtin_before_custom_example (R5): anchor: a valid custom file advertising "light" loses to the builtin
# light (id 2) with no warning; a registered one wins (id 3)
# EXCLUDES: custom files resolved before the builtins
law theme_builtin_before_custom_example:
  {[TChoice.pick([TChoice.Fine{"light", True{}}], "light"), TChoice.pick([TChoice.Fine{"light", False{}}], "light")] == [TChoice.Pick{TName.Res{2, False{}}, None{}, [], []}, TChoice.Pick{TName.Res{3, False{}}, None{}, [], []}] : List<&2, TChoice.Pick>}


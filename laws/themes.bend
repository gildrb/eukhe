# LAWS (T1): themes. Each law is an open claim about the models in
# bend/theme.bend and bend/color.bend; PROOF.bend proves them (as
# Themes.<law>) with the lemmas of bend/proof_themes.bend.

import Base
import ../bend/theme.bend as T
import ../bend/color.bend as Co

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

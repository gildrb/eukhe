# eukhe: the laws of area theme_model: the helpers of the theme model
# (bend/theme/) that the laws of area theme (laws/theme.bend) and the
# entry's spec (spec/theme_wire.bend) read, each pinned to what it means
# (spec/theme_model.bend, written without calling the model). With them
# every model function those laws and specs reach is pinned exactly.

import Base
import ../bend/color.bend as Co
import ../bend/theme/file.bend as TFile
import ../bend/theme/token.bend as TToken
import ../bend/theme/reader.bend as TReader
import ../bend/theme/palette.bend as TPalette
import ../bend/theme/bundled.bend as TBundled
import ../bend/theme/name.bend as TName
import ../bend/ffi_theme.bend as FTh
import ../spec/theme_rules.bend as Ts
import ../spec/theme_model.bend as Tm
import ../spec/theme_wire.bend as Tw

# LAW theme_tok_get_spec (R4): a file's value of a token is the value of its first entry for
# that token, for every file and token
# EXCLUDES: a later entry winning, a value of another token
law theme_tok_get_spec:
  for cols: List<&2, TFile.Ent>
  for +t: U32
  {TToken.get(cols, t) == Tm.tok_get(cols, t) : Maybe<&2, TFile.Val>}

# LAW theme_toks_spec (R4): the tokens are 0 to 58, in order
# EXCLUDES: a token dropped, doubled or reordered (a palette of another
#   length or order)
law theme_toks_spec:
  {TToken.toks() == Tm.toks() : List<&2, U32>}

# LAW theme_required_spec (R3): a token is required exactly when it is none of refinementHeader,
# refinementSummary, mdBody, background, foreground, for every token
# EXCLUDES: an optional token made required or the reverse, past token 58
#   too
law theme_required_spec:
  for +t: U32
  {TReader.required(t) == Tm.required(t) : Bool}

# LAW theme_or_spec (R4): the first set of two optional values, and an optional value with a
# default, for every type
# EXCLUDES: the second value winning, a default over a set value
law theme_or_spec:
  for -A: Data
  for a: Maybe<&2, A>
  for b: Maybe<&2, A>
  for d: A
  {TPalette.or(A, a, b) == Tm.first(A, a, b) : Maybe<&2, A>} & {TPalette.or_else(A, a, d) == Tm.value(A, a, d) : A}

# LAW theme_at_spec (R4): token k of a table is its k-th color (black past its end)
# EXCLUDES: a color of another token
law theme_at_spec:
  for xs: List<&2, Co.Rgb>
  for k: Nat
  {TPalette.at(xs, k) == Ts.get(xs, k) : Co.Rgb}

# LAW theme_concrete_of_spec (R4): the color an optional value paints: none when unset, else the
# value's (theme_concrete_spec)
# EXCLUDES: an unset value painting a color, a set one ignored
law theme_concrete_of_spec:
  for m: Maybe<&2, TFile.Val>
  {TPalette.concrete.of(m) == Tm.concrete_of(m) : Maybe<&2, Co.Rgb>}

# LAW theme_vals_spec (R4): a palette's values are its tokens' values in order, an unset one
# the terminal default
# EXCLUDES: a dropped, reordered or invented value (an empty palette)
law theme_vals_spec:
  for p: List<&2, Maybe<&2, TFile.Val>>
  {TPalette.vals(p) == Tm.vals(p) : List<&2, TFile.Val>}

# LAW theme_fill_map_spec (R4): the palette fills each token of the list in order
# EXCLUDES: a token skipped, reordered or filled with another's value
law theme_fill_map_spec:
  for +cols: List<&2, TFile.Ent>
  for +bg: Co.Rgb
  for ts: List<&2, U32>
  {TPalette.fill.map(cols, bg, ts) == Tm.fmap(cols, bg, ts) : List<&2, Maybe<&2, TFile.Val>>}

# LAW theme_dflt_spec (R5): the default theme is the builtin eukhe, id 0
# EXCLUDES: another default theme
law theme_dflt_spec:
  {TName.dflt() == 0 : U32}

# LAW theme_tables_spec (R4): the colors every token of the shipped themes eukhe, dark and
# light paint
# EXCLUDES: a shipped color changed (a Rust test checks the bundled files
#   paint these)
law theme_tables_spec:
  {[TBundled.table(TBundled.Eukhe{}), TBundled.table(TBundled.Dark{}), TBundled.table(TBundled.Light{})] == [Tm.eukhe(), Tm.dark(), Tm.light()] : List<&2, List<&2, Co.Rgb>>}

# LAW theme_vals_example (R4): anchors: values in order, an unset one the terminal default; a
# valid file loaded through the entry answers its 59 values
# EXCLUDES: an empty palette answered for a valid file
law theme_vals_example:
  {TPalette.vals([Some{TFile.Idx{3}}, None{}, Some{TFile.Hex{Co.Rgb{1, 2, 3}}}]) == [TFile.Idx{3}, TFile.Dflt{}, TFile.Hex{Co.Rgb{1, 2, 3}}] : List<&2, TFile.Val>} & {String.take(FTh.ffi(Tw.req(FTh.Load{Tm.blank()}, "")), 12n) == "1,59,0,0,0,0" : String}

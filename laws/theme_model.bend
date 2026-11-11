# eukhe: the laws of area theme_model: the helpers of the theme model
# (bend/theme/) that the laws of area theme (laws/theme.bend) and the
# entry's spec (spec/theme/wire.bend) state their requirements with. Each
# law here says what a helper means without copying it: by how it splits
# over a list (an appended list is read part by part, one item at a time),
# by Base's Maybe and List functions, by where a value sits in a list, or by
# another function of the model (the reader's missing tokens).
#
# Requirements (R<n> of laws/theme.bend (T1)):
# R3 a file is valid exactly when the reader finds no required token
#    missing (theme_valid_missing); the required tokens themselves are
#    theme_required_tokens (laws/theme.bend).
# R4 the palette: a token's value in a file is its first entry's
#    (theme_tok_get_append, theme_tok_get_one); the tokens are 0 to 58 in
#    order (theme_toks_range); the fallbacks are the first set value and a
#    value's default (theme_or_base, theme_concrete_of_base); token k of a
#    table is its k-th color (theme_at_index); the palette fills, completes
#    and reads its tokens one by one, in order (theme_fill_map_each,
#    theme_complete_each, theme_vals_each).
# R5 the default theme is the builtin eukhe (theme_dflt_eukhe).

import Base
import ../bend/color.bend as Co
import ../bend/theme/file.bend as TFile
import ../bend/theme/token.bend as TToken
import ../bend/theme/reader.bend as TReader
import ../bend/theme/palette.bend as TPalette
import ../bend/theme/name.bend as TName

# LAW theme_tok_get_append (R4): a file's value of token t over two runs of entries is the value the first run gives, else the second's, for every file and token
# EXCLUDES: a later entry winning over an earlier one, an entry dropped
#   from the search
law theme_tok_get_append:
  for xs: List<&2, TFile.Ent>
  for +ys: List<&2, TFile.Ent>
  for +t: U32
  {TToken.get(List.append(&2, TFile.Ent, xs, ys), t) == Maybe.or(&2, TFile.Val, TToken.get(xs, t), TToken.get(ys, t)) : Maybe<&2, TFile.Val>}

# LAW theme_tok_get_one (R4): one entry gives its value to its own token (keys equal as U32) and no value to any other token
# EXCLUDES: a value of another token, a written value ignored
law theme_tok_get_one:
  for +k: U32
  for v: TFile.Val
  for +t: U32
  ({U32.is_eq(k, t) == True{} : Bool} -> {TToken.get([TFile.Ent{k, v}], t) == Some{v} : Maybe<&2, TFile.Val>}) & ({U32.is_eq(k, t) == False{} : Bool} -> {TToken.get([TFile.Ent{k, v}], t) == None{} : Maybe<&2, TFile.Val>})

# the n numbers i, i + 1, ..., as U32
def upto(n: Nat, +i: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      U32.from_nat(i) <> upto(p, 1n+i)

# LAW theme_toks_range (R4): the tokens are the 59 color tokens of crates/eukhe-theme (Token::ALL, ALL[i] == i), 0 to 58, each once, in order
# EXCLUDES: a token dropped, doubled or reordered (a palette of another
#   length or order)
law theme_toks_range:
  {TToken.toks() == upto(59n, 0n) : List<&2, U32>}

# LAW theme_or_base (R4): the fallback of two optional values is the first that is set (Base Maybe.or), and an optional value with a default is the value when set, else the default (Base Maybe.default), for every type
# EXCLUDES: the second value winning, a default over a set value
law theme_or_base:
  for -A: Data
  for a: Maybe<&2, A>
  for b: Maybe<&2, A>
  for d: A
  {TPalette.or(A, a, b) == Maybe.or(&2, A, a, b) : Maybe<&2, A>} & {TPalette.or_else(A, a, d) == Maybe.default(&2, A, a, d) : A}

# LAW theme_concrete_of_base (R4): the color an optional value paints is none when unset, else the color of the value (TToken.concrete, laws/theme.bend theme_concrete_spec): Base Maybe.bind
# EXCLUDES: an unset value painting a color, a set one ignored
law theme_concrete_of_base:
  for m: Maybe<&2, TFile.Val>
  {TPalette.concrete.of(m) == Maybe.bind(&2, TFile.Val, Co.Rgb, m, v => TToken.concrete(v)) : Maybe<&2, Co.Rgb>}

# LAW theme_at_index (R4): token k of a table is the color at place k (counting from 0)
# EXCLUDES: a color of another token (off by one, from the end)
law theme_at_index:
  for +pre: List<&2, Co.Rgb>
  for +c: Co.Rgb
  for post: List<&2, Co.Rgb>
  {TPalette.at(List.append(&2, Co.Rgb, pre, c <> post), List.length(&2, Co.Rgb, pre)) == c : Co.Rgb}

# LAW theme_fill_map_each (R4): the palette of a token list is the palette of each token, in order: two runs of tokens fill as the first run's values then the second's, and one token fills as its own value (TPalette.fill, laws/theme.bend theme_fill_*)
# EXCLUDES: a token skipped, doubled, reordered or filled with another's
#   value
law theme_fill_map_each:
  for +cols: List<&2, TFile.Ent>
  for +bg: Co.Rgb
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for t: U32
  {TPalette.fill.map(cols, bg, List.append(&2, U32, xs, ys)) == List.append(&2, Maybe<&2, TFile.Val>, TPalette.fill.map(cols, bg, xs), TPalette.fill.map(cols, bg, ys)) : List<&2, Maybe<&2, TFile.Val>>} & {TPalette.fill.map(cols, bg, [t]) == [TPalette.fill(cols, bg, t)] : List<&2, Maybe<&2, TFile.Val>>}

# LAW theme_vals_each (R4): a palette's values are its tokens' values in order: two runs of tokens give the first run's values then the second's, a set token its value, an unset one the terminal default
# EXCLUDES: a dropped, reordered or invented value, a set value replaced,
#   an unset token given a color
law theme_vals_each:
  for xs: List<&2, Maybe<&2, TFile.Val>>
  for +ys: List<&2, Maybe<&2, TFile.Val>>
  for v: TFile.Val
  {TPalette.vals(List.append(&2, Maybe<&2, TFile.Val>, xs, ys)) == List.append(&2, TFile.Val, TPalette.vals(xs), TPalette.vals(ys)) : List<&2, TFile.Val>} & {[TPalette.vals([Some{v}]), TPalette.vals([None{}])] == [[v], [TFile.Dflt{}]] : List<&2, List<&2, TFile.Val>>}

# LAW theme_complete_each (R4): a palette is complete exactly when every token has a value: two runs are complete when both are, a set token is, an unset one is not
# EXCLUDES: a completeness test that always fails or always holds, or that
#   skips a token (theme_tokens_complete made vacuous)
law theme_complete_each:
  for xs: List<&2, Maybe<&2, TFile.Val>>
  for +ys: List<&2, Maybe<&2, TFile.Val>>
  for v: TFile.Val
  {TPalette.complete(List.append(&2, Maybe<&2, TFile.Val>, xs, ys)) == Bool.and(TPalette.complete(xs), TPalette.complete(ys)) : Bool} & {[TPalette.complete([Some{v}]), TPalette.complete([None{}])] == [True{}, False{}] : List<&2, Bool>}

# LAW theme_dflt_eukhe (R5): the default theme is the builtin named eukhe: its id names the valid builtin "eukhe" among the builtins
# EXCLUDES: another default theme, a default id no builtin carries
law theme_dflt_eukhe:
  {List.get(&2, TName.Cand, TName.builtins(), U32.to_nat(TName.dflt())) == Some{TName.Cand{"eukhe", True{}, TName.dflt()}} : Maybe<&2, TName.Cand>}

# LAW theme_valid_missing (R3): a file is valid exactly when the reader finds no required token missing from its colors (TReader.missing, laws/theme.bend theme_read_missing), whatever its name and export backgrounds; mdBody's fallback to text then always holds, text being required
# EXCLUDES: a validity test that always fails or always holds, or that
#   checks other tokens than the required ones (theme_load_valid,
#   theme_tokens_complete made vacuous)
law theme_valid_missing:
  for nm: String
  for +cols: List<&2, TFile.Ent>
  for pg: Maybe<&2, Co.Rgb>
  for cd: Maybe<&2, Co.Rgb>
  for io: Maybe<&2, Co.Rgb>
  {TToken.valid(TFile.Th{nm, cols, pg, cd, io}) == List.is_empty(&2, U32, TReader.missing(cols)) : Bool}

# LAW theme_vals_example (R4): anchor: values in order, an unset one the terminal default
# EXCLUDES: an empty palette answered for a valid file
law theme_vals_example:
  {TPalette.vals([Some{TFile.Idx{3}}, None{}, Some{TFile.Hex{Co.Rgb{1, 2, 3}}}]) == [TFile.Idx{3}, TFile.Dflt{}, TFile.Hex{Co.Rgb{1, 2, 3}}] : List<&2, TFile.Val>}

# a file that writes every required token as the terminal default
def blank.keep(keep: Bool, t: U32, rest: List<&2, TFile.REnt>) -> List<&2, TFile.REnt>:
  match keep:
    case True{}:
      TFile.REnt{"k", Some{t}, TFile.JStr{"", None{}}} <> rest
    case False{}:
      rest

def blank.cols(ts: List<&2, U32>) -> List<&2, TFile.REnt>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      blank.keep(TReader.required(t), t, blank.cols(rest))

def blank() -> TFile.RFile:
  TFile.RFile{"blank", [], blank.cols(TToken.toks()), None{}, None{}, None{}}

# LAW theme_valid_example (R3): anchors: the file with every required token written loads and
# is valid; a file with no colors is not valid; a palette with an unset
# token is not complete
# EXCLUDES: a reading of the laws above the human did not mean
law theme_valid_example:
  {Maybe.is_some(&2, TFile.Th, TReader.load(blank())) == True{} : Bool} & {TToken.valid(TFile.Th{"e", [], None{}, None{}, None{}}) == False{} : Bool} & {[TPalette.complete([Some{TFile.Dflt{}}, None{}]), TPalette.complete([Some{TFile.Dflt{}}])] == [False{}, True{}] : List<&2, Bool>}

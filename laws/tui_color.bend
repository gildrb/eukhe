# eukhe: the laws of area tui_color

import Base
import ../bend/color.bend as Co
import ../bend/ffi_tui_color.bend as FTC
import ../bend/theme/bundled.bend as TBundled
import ../bend/theme/file.bend as TFile
import ../bend/tui_color.bend as TC
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- tui_color ----

# LAWS (T3): terminal colors. Each law is an open claim about the model
# in bend/tui_color.bend (with the theme tables of bend/theme/bundled.bend)
# or about its entry bend/ffi_tui_color.bend (section entry); PROOF.bend
# proves them (as TuiColor.<law>) with the lemmas of proof/tui_color/.

# (T3) Terminal colors
# --------------------
# The model in bend/tui_color.bend:
# the effort ramp, the usage bands and the color roles of
# crates/eukhe-tui. Every input is free: any ramp ends and any ladder
# length, any token count and any window. The terminal UI runs the model
# itself, through the entry bend/ffi_tui_color.bend (section entry).
#
# Requirements (T3 is this area's tag; omp = oh-my-pi c28b3e3)
# R1 The effort ramp (crates/eukhe-tui/src/theme.rs:542-546 effort_ramp,
#    bend/tui_color.bend:7-12): a ladder of n levels gets n rungs, lowest
#    first, from the theme's effortLow toward its effortHigh; rung k
#    (1 to n) is, in each channel, the point k/n of the way from effortLow
#    to effortHigh rounded down, so rung n is effortHigh; every channel
#    moves one way along the ramp; the rungs are distinct when one channel
#    of the ends is at least n apart, and in every shipped theme for every
#    ladder of the level vocabulary (7 levels). omp has no effort ramp.
#    Laws: tui_effort_ramp_length, tui_effort_ramp_lerp,
#    tui_effort_ramp_ordered, tui_effort_ramp_distinct,
#    tui_effort_shipped_distinct; anchors tui_effort_ladder_max_exact,
#    tui_effort_ramp_teeth_example.
# R2 The usage band (omp packages/tui/src/chrome/context-thresholds.ts:
#    6-11,13-56 getContextUsageLevel, contextPercent = 100 t / w as in
#    packages/tui/src/status-line/component.ts:2664-2667; crates/eukhe-tui
#    status_line.rs context_color): t tokens in a w-token window give 0
#    (normal) for an unknown window (0), else 3 (error) from 90% of the
#    window, 2 from 70%, 1 (warning) from 50%, 0 below, each percent
#    reached exactly at it. omp's token thresholds (150k, 270k, 500k
#    tokens, whichever comes first) are NOT modeled: eukhe colors by the
#    percents only, so above a 300k window it colors later than omp (an
#    open gap, reported, not a law). Laws: tui_usage_band_omp,
#    tui_usage_band_monotone, tui_usage_band_fraction, tui_usage_band_full,
#    tui_usage_bands_ascend; anchor tui_usage_bands_ascend_teeth_example.
# R3 The roles (crates/eukhe-tui/src/theme.rs:84-298, crates/eukhe-theme/
#    src/token.rs:5-196): every color slot of the terminal UI, in Rust's
#    slot order (ThemeColor::ALL, ThemeBg::ALL, ThemeRgb::ALL), is painted
#    by the token of the same key (the canvas by background); the 58 slots
#    take 58 distinct tokens, every token but foreground; every role has a
#    color in every shipped theme; a role paints in a color table exactly
#    when its index is inside the table, and resolves in a palette exactly
#    when its entry there has a value. Laws: tui_roles_by_name,
#    tui_roles_cover, tui_roles_shipped, tui_paints_bound,
#    tui_resolves_split, tui_resolves_at, tui_resolves_past (and
#    tui_roles_resolve of laws/theme.bend); anchors
#    tui_roles_paint_teeth_example, tui_resolves_example.
# R4 The entry (bend/ffi_tui_color.bend, crates/eukhe-bend/WIRE.md,
#    crates/eukhe-bend/src/rules/tui_color.rs): a request spelled with the
#    wire primitives; a ramp whose channels and rung count are at most 255
#    answers the model's rungs, any other ramp the range error; a band the
#    model's band; the roles the model's roles; a request with input left
#    over, and every input that is not exactly one request, the malformed
#    error. Laws: tui_color_ffi_ramp, tui_color_ffi_ramp_range,
#    tui_color_ffi_band, tui_color_ffi_roles, tui_color_ffi_left_over,
#    tui_color_ffi_total; anchors tui_color_ffi_premises_example,
#    tui_color_ffi_example.

# LAW tui_effort_ramp_length: the effort ramp has one rung for each level the model offers
law tui_effort_ramp_length:
  for lo: TC.Px
  for hi: TC.Px
  for n: Nat
  {List.length(&2, TC.Px, TC.ramp(lo, hi, n)) == n : Nat}

# LAW tui_effort_ramp_ordered: for any ladder length, along the effort ramp every channel moves
# from the low end toward the high end, never back
law tui_effort_ramp_ordered:
  for lo: TC.Px
  for hi: TC.Px
  for n: Nat
  {TC.ordered(lo, hi, TC.ramp(lo, hi, n)) == True{} : Bool}

# LAW tui_effort_ramp_distinct: for any ladder length up to the widest channel distance of the
# ends, no two rungs of the effort ramp have the same color
law tui_effort_ramp_distinct:
  for lo: TC.Px
  for hi: TC.Px
  for n: Nat
  for fits: {Nat.is_le(n, TC.span(lo, hi)) == True{} : Bool}
  {TC.distinct(TC.ramp(lo, hi, n)) == True{} : Bool}

# LAW tui_effort_shipped_distinct: in every shipped theme, no two rungs of the effort ramp have the
# same color, for any ladder of the level vocabulary
law tui_effort_shipped_distinct:
  for s: TBundled.Shipped
  for n: Nat
  for fits: {Nat.is_le(n, TC.ladder.max()) == True{} : Bool}
  {TC.distinct(TC.ramp(TC.shipped.lo(s), TC.shipped.hi(s), n)) == True{} : Bool}

# LAW tui_effort_ladder_max_exact: the longest ladder of tui_effort_shipped_distinct is the whole level vocabulary: off, minimal, low, medium, high, xhigh, max (7 levels)
# EXCLUDES: a vacuous tui_effort_shipped_distinct (a bound of 0 or 1
#   rung, which every ramp meets)
law tui_effort_ladder_max_exact:
  {TC.ladder.max() == 7n : Nat}

# LAW tui_usage_bands_ascend: every usage band is a fraction of the window above zero and at
# most one, and each band is above the band before it
law tui_usage_bands_ascend:
  {TC.ascend(TC.bands()) == True{} : Bool}

# LAW tui_usage_band_monotone: more tokens in the same window never give a lower usage band
law tui_usage_band_monotone:
  for t: Nat
  for e: Nat
  for w: Nat
  {Nat.is_le(TC.band(t, w), TC.band(Nat.add(t, e), w)) == True{} : Bool}

# LAW tui_usage_band_fraction: the usage band depends only on the fraction of the window in use:
# the same fraction of a window k times as large gives the same band
law tui_usage_band_fraction:
  for k: Nat
  for t: Nat
  for w: Nat
  {TC.band(Nat.mul(1n+k, t), Nat.mul(1n+k, w)) == TC.band(t, w) : Nat}

# LAW tui_usage_band_full: tokens at or past the window reach what the full window reaches,
# so the caller may cap the tokens at the window (and at any cap at or
# above the window) without changing the band
# EXCLUDES: a band that changes past the full window (an overflow, a
#   wrap, a fraction above one read as more)
law tui_usage_band_full:
  for +t: Nat
  for +w: Nat
  for +past: {Nat.is_le(w, t) == True{} : Bool}
  {TC.band(t, w) == TC.band(w, w) : Nat}

# LAW tui_roles_shipped: every color role of the terminal UI paints a color in every
# shipped theme
law tui_roles_shipped:
  for s: TBundled.Shipped
  {TC.paints(TBundled.table(s), TC.roles()) == True{} : Bool}

# rung j of an n-rung ramp from a to b in one channel: the point j/n of
# the way from a to b, rounded down, floor((a (n - j) + b j) / n). It
# weighs the two ends, with no case for the direction of the channel.
def lerp(+a: Nat, +b: Nat, +j: Nat, +n: Nat) -> Nat:
  Nat.div(Nat.add(Nat.mul(a, Nat.sub(n, j)), Nat.mul(b, j)), n)

# rung j of an n-rung ramp from lo to hi, channel by channel
def lerp_px(lo: TC.Px, hi: TC.Px, +j: Nat, +n: Nat) -> TC.Px:
  match lo hi:
    case TC.Px{lr, lg, lb} TC.Px{hr, hg, hb}:
      TC.Px{lerp(lr, hr, j, n), lerp(lg, hg, j, n), lerp(lb, hb, j, n)}

# LAW tui_effort_ramp_lerp (R1): for every ends lo and hi and every ladder length n, rung k + 1 of the effort ramp (k below n) is, in each channel, the point (k + 1)/n of the way from lo to hi rounded down, floor((a (n - k - 1) + b (k + 1)) / n) for the channel's ends a (lo) and b (hi); so the last rung is hi
# EXCLUDES: a ramp that is ordered and distinct but not evenly spaced:
#   rungs shifted by one, lo as the first rung, hi missing, rounding up or
#   to nearest, a falling channel rounded toward the other end, another
#   spacing; with tui_effort_ramp_length it pins every rung
law tui_effort_ramp_lerp:
  for +lo: TC.Px
  for +hi: TC.Px
  for +n: Nat
  for +k: Nat
  for lt: {Nat.is_lt(k, n) == True{} : Bool}
  {List.get(&2, TC.Px, TC.ramp(lo, hi, n), k) == Some{lerp_px(lo, hi, 1n+k, n)} : Maybe<&2, TC.Px>}

# t of w tokens reach p percent of the window: t / w * 100 >= p, that is
# w p <= 100 t (omp reachesThreshold, percent part)
def omp_reaches(+t: Nat, +w: Nat, p: Nat) -> Bool:
  Nat.is_le(Nat.mul(w, p), Nat.mul(t, 100n))

# omp getContextUsageLevel, from the top: error (3) at 90%, purple (2) at
# 70%, warning (1) at 50%, else normal (0)
def omp_level.from(error: Bool, purple: Bool, warning: Bool) -> Nat:
  match error:
    case True{}:
      3n
    case False{}:
      match purple:
        case True{}:
          2n
        case False{}:
          match warning:
            case True{}:
              1n
            case False{}:
              0n

# the context usage level of t tokens in a w-token window by omp's
# percent thresholds; an unknown window (0) is normal (omp: no percent)
def omp_level(+t: Nat, w: Nat) -> Nat:
  match w:
    case 0n:
      0n
    case 1n+v:
      +x = {1n+v : Nat}
      omp_level.from(omp_reaches(t, x, 90n), omp_reaches(t, x, 70n), omp_reaches(t, x, 50n))

# LAW tui_usage_band_omp (R2): the usage band of t tokens in a w-token window is omp's context usage level by its percent thresholds: 0 for an unknown window (0); else 3 when t is at least 90% of w, 2 at least 70%, 1 at least 50%, 0 below, each percent reached exactly at it. omp's token thresholds (150k, 270k, 500k tokens) are not part of the claim: the band ignores them
# EXCLUDES: other shares (the bands' own laws hold for any ascending
#   shares in (0, 1]), a share reached only past its percent, tokens and
#   window swapped, a band for an unknown window, levels in another order
law tui_usage_band_omp:
  for +t: Nat
  for +w: Nat
  {TC.band(t, w) == omp_level(t, w) : Nat}

def roles_below(xs: List<&2, Nat>, +m: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Bool.and(Nat.is_lt(x, m), roles_below(rest, m))

def roles_absent(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Bool.and(Bool.not(Nat.is_eq(x, y)), roles_absent(x, rest))

def roles_distinct(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(roles_absent(x, rest), roles_distinct(rest))

# LAW tui_roles_cover: the color roles are 58 distinct tokens, each below 58: every token but the foreground (58) colors exactly one slot of the terminal UI
# EXCLUDES: two slots painted by one token (a slot given its neighbour's
#   color), a token no slot paints, a role past the token table
law tui_roles_cover:
  {List.length(&2, Nat, TC.roles()) == 58n : Nat} & {roles_below(TC.roles(), 58n) == True{} : Bool} & {roles_distinct(TC.roles()) == True{} : Bool}

# the key of every token, in the order of crates/eukhe-theme/src/token.rs
# Token::ALL (its index is the token's index): Token::name, lines 134-195
def token_keys() -> List<&2, String>:
  ["accent", "border", "borderAccent", "borderMuted", "success", "error", "warning", "muted", "dim", "text", "thinkingText", "userMessageText", "customMessageText", "customMessageLabel", "refinementHeader", "refinementSummary", "toolTitle", "toolOutput", "mdBody", "mdHeading", "mdLink", "mdLinkUrl", "mdCode", "mdCodeBlock", "mdCodeBlockBorder", "mdQuote", "mdQuoteBorder", "mdHr", "mdListBullet", "toolDiffAdded", "toolDiffRemoved", "toolDiffText", "toolDiffContext", "syntaxComment", "syntaxKeyword", "syntaxFunction", "syntaxVariable", "syntaxString", "syntaxNumber", "syntaxType", "syntaxOperator", "syntaxPunctuation", "effortLow", "effortHigh", "contextHigh", "liftLight", "liftDark", "bashMode", "selectedBg", "userMessageBg", "customMessageBg", "toolPendingBg", "toolSuccessBg", "toolErrorBg", "toolDiffAddedBg", "toolDiffRemovedBg", "toolPanelBg", "background", "foreground"]

# the key of every color slot of the terminal UI, in the order the Rust
# slot tables index the roles (crates/eukhe-tui/src/theme.rs Roles::
# from_core, lines 285-297): ThemeColor::ALL (lines 134-179), then
# ThemeBg::ALL (201-211), then ThemeRgb::ALL (233-239); each slot's key is
# its variant name in lower camel case, the canvas's the background
# (theme.rs:218-221)
def slot_keys() -> List<&2, String>:
  ["accent", "border", "borderAccent", "borderMuted", "success", "error", "warning", "muted", "dim", "text", "thinkingText", "userMessageText", "customMessageText", "customMessageLabel", "refinementHeader", "refinementSummary", "toolTitle", "toolOutput", "mdBody", "mdHeading", "mdLink", "mdLinkUrl", "mdCode", "mdCodeBlock", "mdCodeBlockBorder", "mdQuote", "mdQuoteBorder", "mdHr", "mdListBullet", "toolDiffAdded", "toolDiffRemoved", "toolDiffText", "toolDiffContext", "syntaxComment", "syntaxKeyword", "syntaxFunction", "syntaxVariable", "syntaxString", "syntaxNumber", "syntaxType", "syntaxOperator", "syntaxPunctuation", "contextHigh", "bashMode", "selectedBg", "userMessageBg", "customMessageBg", "toolPendingBg", "toolSuccessBg", "toolErrorBg", "toolDiffAddedBg", "toolDiffRemovedBg", "toolPanelBg", "effortLow", "effortHigh", "liftLight", "liftDark", "background"]

# the key at index r of ks ("" past its end)
def key_at(ks: List<&2, String>, r: Nat) -> String:
  match ks r:
    case Nil{} _:
      ""
    case Con{k, t} 0n:
      k
    case Con{k, t} 1n+j:
      key_at(t, j)

# the token key of every token index of rs
def keys_of(rs: List<&2, Nat>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, rest}:
      key_at(token_keys(), r) <> keys_of(rest)

# LAW tui_roles_by_name (R3): each color slot of the terminal UI, in the order Rust's slot tables read the roles, is painted by the token of the same key: the token keys (crates/eukhe-theme token.rs) of the roles are the slot keys of ThemeColor, ThemeBg and ThemeRgb (crates/eukhe-tui theme.rs) in declaration order, the canvas painted by background. Both key tables are transcribed from the Rust sources named above them
# EXCLUDES: slots that swap tokens (tui_roles_cover and the palette laws
#   hold for any order): a slot painted with another slot's color, a
#   surface painted with an ink token, the ramp or lift ends swapped
law tui_roles_by_name:
  {keys_of(TC.roles()) == slot_keys() : List<&2, String>}

# LAW tui_usage_bands_ascend_teeth_example: the ascent test of tui_usage_bands_ascend refuses shares out of order, a repeated share, a share of 0 and a share above the whole window, first or later
# EXCLUDES: a vacuous tui_usage_bands_ascend (an ascent test that holds
#   for any shares)
law tui_usage_bands_ascend_teeth_example:
  {TC.ascend([TC.Frac{7n, 10n}, TC.Frac{1n, 2n}]) == False{} : Bool} &
  {TC.ascend([TC.Frac{1n, 2n}, TC.Frac{2n, 4n}]) == False{} : Bool} &
  {TC.ascend([TC.Frac{1n, 2n}, TC.Frac{0n, 3n}]) == False{} : Bool} &
  {TC.ascend([TC.Frac{1n, 2n}, TC.Frac{4n, 3n}]) == False{} : Bool} &
  {TC.ascend([TC.Frac{1n, 2n}, TC.Frac{7n, 10n}, TC.Frac{3n, 5n}]) == False{} : Bool} &
  {TC.ascend([TC.Frac{0n, 2n}, TC.Frac{1n, 2n}]) == False{} : Bool} &
  {TC.ascend([TC.Frac{4n, 3n}]) == False{} : Bool} &
  {TC.ascend([TC.Frac{1n, 3n}, TC.Frac{1n, 2n}, TC.Frac{1n, 1n}]) == True{} : Bool}

# LAW tui_effort_ramp_teeth_example: the tests of tui_effort_ramp_ordered and tui_effort_ramp_distinct refuse a channel that moves back, a repeated color, and measure the widest channel distance
# EXCLUDES: a vacuous tui_effort_ramp_ordered or tui_effort_ramp_distinct
#   (an order or distinctness test that holds for any rungs, a span of 0)
law tui_effort_ramp_teeth_example:
  {TC.span(TC.Px{0n, 9n, 200n}, TC.Px{10n, 6n, 0n}) == 200n : Nat} &
  {TC.ordered(TC.Px{0n, 9n, 0n}, TC.Px{10n, 0n, 0n}, [TC.Px{5n, 5n, 0n}, TC.Px{4n, 4n, 0n}]) == False{} : Bool} &
  {TC.ordered(TC.Px{0n, 9n, 0n}, TC.Px{10n, 0n, 0n}, [TC.Px{5n, 5n, 0n}, TC.Px{6n, 6n, 0n}]) == False{} : Bool} &
  {TC.ordered(TC.Px{0n, 9n, 0n}, TC.Px{10n, 0n, 0n}, [TC.Px{5n, 5n, 0n}, TC.Px{6n, 4n, 0n}, TC.Px{6n, 4n, 0n}]) == True{} : Bool} &
  {TC.distinct([TC.Px{1n, 2n, 3n}, TC.Px{4n, 5n, 6n}, TC.Px{1n, 2n, 3n}]) == False{} : Bool} &
  {TC.distinct([TC.Px{1n, 2n, 3n}, TC.Px{1n, 2n, 4n}, TC.Px{1n, 3n, 3n}]) == True{} : Bool}

# LAW tui_roles_paint_teeth_example: the tests of tui_roles_shipped and tui_roles_resolve refuse a role past the table, a role with no value and a role whose value is missing, and accept a role that has one
# EXCLUDES: a vacuous tui_roles_shipped or tui_roles_resolve (a test that
#   holds for any table)
law tui_roles_paint_teeth_example:
  {TC.paints([Co.Rgb{1, 2, 3}], [0n, 1n]) == False{} : Bool} &
  {TC.paints([Co.Rgb{1, 2, 3}], [0n]) == True{} : Bool} &
  {TC.resolves([Some{TFile.Dflt{}}], [0n, 1n]) == False{} : Bool} &
  {TC.resolves([None{}, Some{TFile.Dflt{}}], [1n, 0n]) == False{} : Bool} &
  {TC.resolves([None{}, Some{TFile.Dflt{}}], [1n]) == True{} : Bool}

# ---- entry ----

# LAWS: the entry of the compiled Bend core that runs the terminal colors
# (bend/ffi_tui_color.bend, called by crates/eukhe-tui through
# crates/eukhe-bend/src/rules/tui_color.rs). Each law is an open claim
# about FTC.ffi, the function the core runs, stated with spec spellers
# built only from the wire primitives of bend/wire.bend (their round
# trips: laws/wire.bend).

# The entry
# ---------
# A request is a ramp (two colors and a rung count), a band (the tokens
# and the window) or the roles. The entry answers the model's ramp, band
# and roles. A ramp with a channel above 255 or more than 255 rungs
# answers the range error; every other input that is not exactly one
# request answers the malformed error. Every input is free.

# Spec spellers
# -------------

def spell_px(p: TC.Px, rest: String) -> String:
  match p:
    case TC.Px{r, g, b}:
      Wr.put_nat(r, Wr.put_nat(g, Wr.put_nat(b, rest)))

# a request: its tag (0 ramp, 1 band, 2 roles), then its fields, then rest
def spell_req(q: FTC.Req, rest: String) -> String:
  match q:
    case FTC.QRamp{lo, hi, n}:
      Wr.put_nat(0n, spell_px(lo, spell_px(hi, Wr.put_nat(n, rest))))
    case FTC.QBand{t, w}:
      Wr.put_nat(1n, Wr.put_nat(t, Wr.put_nat(w, rest)))
    case FTC.QRoles{}:
      Wr.put_nat(2n, rest)

def spell_rungs.items(xs: List<&2, TC.Px>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      spell_px(x, spell_rungs.items(rest))

# a list of colors: its count, then each color's red, green and blue
def spell_rungs(+xs: List<&2, TC.Px>) -> String:
  Wr.put_nat(List.length(&2, TC.Px, xs), spell_rungs.items(xs))

def spell_nats.items(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      Wr.put_nat(x, spell_nats.items(rest))

# a list of Nats: its count, then each one
def spell_nats(+xs: List<&2, Nat>) -> String:
  Wr.put_nat(List.length(&2, Nat, xs), spell_nats.items(xs))

def px_fits(p: TC.Px) -> Bool:
  match p:
    case TC.Px{r, g, b}:
      Bool.and(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(g), LawsBase.wire_fits(b)))

# every number of a request fits the wire
def req_fits(q: FTC.Req) -> Bool:
  match q:
    case FTC.QRamp{lo, hi, n}:
      Bool.and(px_fits(lo), Bool.and(px_fits(hi), LawsBase.wire_fits(n)))
    case FTC.QBand{t, w}:
      Bool.and(LawsBase.wire_fits(t), LawsBase.wire_fits(w))
    case FTC.QRoles{}:
      True{}

def px_in(p: TC.Px) -> Bool:
  match p:
    case TC.Px{r, g, b}:
      Bool.and(Nat.is_le(r, 255n), Bool.and(Nat.is_le(g, 255n), Nat.is_le(b, 255n)))

# a ramp the entry draws: every channel of both ends at most 255, at most
# 255 rungs
def ramp_in(lo: TC.Px, hi: TC.Px, n: Nat) -> Bool:
  Bool.and(px_in(lo), Bool.and(px_in(hi), Nat.is_le(n, 255n)))

def range_err() -> String:
  SCon{'E', SCon{' ', "tui_color: a channel above 255 or more than 255 rungs"}}

def malformed_err() -> String:
  SCon{'E', SCon{' ', "tui_color: malformed request"}}

# Laws
# ----

# LAW tui_color_ffi_ramp: a ramp request whose channels and rung count are at most 255 answers the model's ramp: its rungs, lowest first, each as red, green and blue
# EXCLUDES: a ramp that is not the model's, rungs lost, added or
#   reordered, channels swapped, the ends swapped, a field of the request
#   misread
law tui_color_ffi_ramp:
  for +lo: TC.Px
  for +hi: TC.Px
  for +n: Nat
  for fit: {req_fits(FTC.QRamp{lo, hi, n}) == True{} : Bool}
  for in: {ramp_in(lo, hi, n) == True{} : Bool}
  {FTC.ffi(spell_req(FTC.QRamp{lo, hi, n}, "")) == spell_rungs(TC.ramp(lo, hi, n)) : String}

# LAW tui_color_ffi_ramp_range: a ramp request that fits the wire with a channel above 255 or more than 255 rungs answers exactly the range error
# EXCLUDES: a ramp of a color no terminal paints, a clamped or wrapped
#   channel, a ramp too long to have distinct rungs, a range error spelled
#   with another text
law tui_color_ffi_ramp_range:
  for +lo: TC.Px
  for +hi: TC.Px
  for +n: Nat
  for fit: {req_fits(FTC.QRamp{lo, hi, n}) == True{} : Bool}
  for out: {ramp_in(lo, hi, n) == False{} : Bool}
  {FTC.ffi(spell_req(FTC.QRamp{lo, hi, n}, "")) == range_err() : String}

# LAW tui_color_ffi_band: a band request answers the model's usage band of the tokens in the window, for every token count and window the wire carries
# EXCLUDES: a band that is not the model's (tokens and window swapped,
#   another share, a rounding off by one at a share's edge), a refusal of
#   a large window
# LEAVES FREE: the size of the numbers the entry computes on the way: the
#   law is over Nat, so an entry that multiplies t by a share's
#   denominator passes it and stops at run time past 2^48 - 1. The entry
#   computes no product past the window (FTC.need); the Rust test
#   crates/eukhe-bend/src/rules/tui_color.rs runs the largest window the
#   wire carries through the compiled core.
law tui_color_ffi_band:
  for +t: Nat
  for +w: Nat
  for fit: {req_fits(FTC.QBand{t, w}) == True{} : Bool}
  {FTC.ffi(spell_req(FTC.QBand{t, w}, "")) == Wr.put_nat(TC.band(t, w), "") : String}

# LAW tui_color_ffi_roles: the roles request answers the model's roles: the token index of every color slot, in slot order
# EXCLUDES: a role lost, added, reordered or changed
law tui_color_ffi_roles:
  {FTC.ffi(spell_req(FTC.QRoles{}, "")) == spell_nats(TC.roles()) : String}

# LAW tui_color_ffi_left_over: a request followed by any more input answers exactly the malformed error
# EXCLUDES: an entry that answers the request and ignores what follows
law tui_color_ffi_left_over:
  for +q: FTC.Req
  for fit: {req_fits(q) == True{} : Bool}
  for c: Char
  for rest: String
  {FTC.ffi(spell_req(q, SCon{c, rest})) == malformed_err() : String}

# LAW tui_color_ffi_premises_example: the premises of the entry laws hold for real requests: a ramp of the light theme's ends is in range, one with a channel of 256 is not, and a roles request answers something other than the malformed error
# EXCLUDES: a vacuous tui_color_ffi_ramp, tui_color_ffi_ramp_range or
#   tui_color_ffi_total
law tui_color_ffi_premises_example:
  {ramp_in(TC.Px{135n, 95n, 135n}, TC.Px{139n, 0n, 139n}, 3n) == True{} : Bool} &
  {ramp_in(TC.Px{0n, 0n, 0n}, TC.Px{256n, 0n, 0n}, 1n) == False{} : Bool} &
  {String.eq(FTC.ffi("2,"), malformed_err()) == False{} : Bool}

# LAW tui_color_ffi_example: anchor: the bytes Rust sends and reads: the light theme's 3-rung effort ramp, a channel of 256 refused, 64 of 128 tokens (band 1), tokens in an unknown window (band 0), 89 and 90 of 100 tokens (bands 2 and 3), a roles request with a byte left over
# EXCLUDES: another spelling of a request or of a reply, a rounding off
#   by one at a share's edge
law tui_color_ffi_example:
  {FTC.ffi("0,135,95,135,139,0,139,3,") == "3,136,63,136,137,31,137,139,0,139," : String} &
  {FTC.ffi("0,0,0,0,256,0,0,1,") == range_err() : String} &
  {FTC.ffi("1,64,128,") == "1," : String} &
  {FTC.ffi("1,5,0,") == "0," : String} &
  {FTC.ffi("1,89,100,") == "2," : String} &
  {FTC.ffi("1,90,100,") == "3," : String} &
  {FTC.ffi("2,x") == malformed_err() : String}

# The whole entry
# ---------------
# What the entry answers to every input, from the spec spellers above: an
# input that answers anything but the malformed error is exactly the
# spelling of one request that fits the wire, and the answer is the reply
# to it: the ramp TC.ramp (pinned for every input by tui_effort_ramp_length
# and tui_effort_ramp_lerp) or the range error, the band omp_level
# (omp's percent thresholds) and the roles TC.roles (pinned by
# tui_roles_by_name).

def tc_reply.ramp(in: Bool, +lo: TC.Px, +hi: TC.Px, +n: Nat) -> String:
  match in:
    case True{}:
      spell_rungs(TC.ramp(lo, hi, n))
    case False{}:
      range_err()

# the reply to a request
def tc_reply(q: FTC.Req) -> String:
  match q:
    case FTC.QRamp{+lo, +hi, +n}:
      tc_reply.ramp(ramp_in(lo, hi, n), lo, hi, n)
    case FTC.QBand{+t, w}:
      Wr.put_nat(omp_level(t, w), "")
    case FTC.QRoles{}:
      spell_nats(TC.roles())

# LAW tui_color_ffi_total (R4): every input that answers anything but the malformed error is exactly the spelling of one request whose numbers fit the wire, and its answer is the reply to that request: a ramp in range its rungs, out of range the range error; a band omp's usage level of its tokens in its window; the roles the role list. With tui_color_ffi_ramp, tui_color_ffi_ramp_range, tui_color_ffi_band and tui_color_ffi_roles (no request answers the malformed error) this pins the answer to every input
# EXCLUDES: an entry that answers an input that is not exactly one request
#   (an unknown tag, a field missing, a number malformed or too long, a
#   number spelled another way, input left over) with anything but the
#   malformed error (a default ramp, band or roles, the range error), a
#   reply off the spec for a request read from such an input
law tui_color_ffi_total:
  for +s: String
  for other: {String.eq(FTC.ffi(s), malformed_err()) == False{} : Bool}
  exs q: FTC.Req
  {(s, (req_fits(q), FTC.ffi(s))) == (spell_req(q, ""), (True{}, tc_reply(q))) : String & (Bool & String)}

# xs then ys
def cat(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      ys
    case Con{x, rest}:
      x <> cat(A, rest, ys)

# LAW tui_resolves_split (R3): no roles resolve in every palette, and the roles xs then ys resolve exactly when xs resolve and ys resolve
# EXCLUDES: a test that reads one role for another or lets a later role
#   decide for an earlier one (only the first role checked, the last one
#   ignored)
law tui_resolves_split:
  for +p: List<&2, Maybe<&2, TFile.Val>>
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  {TC.resolves(p, Nil{}) == True{} : Bool} & {TC.resolves(p, cat(Nat, xs, ys)) == Bool.and(TC.resolves(p, xs), TC.resolves(p, ys)) : Bool}

# LAW tui_resolves_at (R3): the role i resolves in the palette p, then the entry x, then q (i the length of p) exactly when x has a value
# EXCLUDES: a test that always holds (tui_roles_resolve made vacuous), a
#   role looked up at another token, an unset token that resolves
law tui_resolves_at:
  for +p: List<&2, Maybe<&2, TFile.Val>>
  for +x: Maybe<&2, TFile.Val>
  for +q: List<&2, Maybe<&2, TFile.Val>>
  {TC.resolves(cat(Maybe<&2, TFile.Val>, p, x <> q), [List.length(&2, Maybe<&2, TFile.Val>, p)]) == Maybe.is_some(&2, TFile.Val, x) : Bool}

# LAW tui_resolves_past (R3): a role at or past the end of the palette does not resolve
# EXCLUDES: a role past the palette read as set (a wrapped index, a
#   default value)
law tui_resolves_past:
  for +p: List<&2, Maybe<&2, TFile.Val>>
  for +r: Nat
  for past: {Nat.is_le(List.length(&2, Maybe<&2, TFile.Val>, p), r) == True{} : Bool}
  {TC.resolves(p, [r]) == False{} : Bool}

# LAW tui_resolves_example: anchors: an unset token does not resolve, a set one does, a token
# past the palette does not
# EXCLUDES: a reading of tui_resolves_at and tui_resolves_past the human did
#   not mean
law tui_resolves_example:
  {[TC.resolves([None{}], [0n]), TC.resolves([Some{TFile.Dflt{}}], [0n]), TC.resolves([Some{TFile.Dflt{}}], [1n])] == [False{}, True{}, False{}] : List<&2, Bool>}

# LAW tui_paints_bound (R3): the roles paint in a color table exactly when every role index is below the length of the table
# EXCLUDES: a test that always holds for some tables (tui_roles_shipped
#   made vacuous, e.g. one that holds for any table of 2 or more colors),
#   a role looked up at another token, a role past the table that paints
law tui_paints_bound:
  for +xs: List<&2, Co.Rgb>
  for +rs: List<&2, Nat>
  {TC.paints(xs, rs) == roles_below(rs, List.length(&2, Co.Rgb, xs)) : Bool}

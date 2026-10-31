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
# in bend/tui_color.bend (with the theme tables of bend/theme/bundled.bend);
# PROOF.bend proves them (as TuiColor.<law>) with the lemmas of
# proof/tui_color/.

# (T3) Terminal colors
# --------------------
# The model in bend/tui_color.bend:
# the effort ramp, the usage bands and the color roles of
# crates/eukhe-tui. Every input is free: any ramp ends and any ladder
# length, any token count and any window. The terminal UI runs the model
# itself, through the entry bend/ffi_tui_color.bend (section entry).

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

# rung k (1 to n) of the ramp from a to b in one channel: the lower end
# plus floor(d * w / n), d = |b - a|, w = k when the channel rises (a <= b)
# and n - k when it falls, so rung n is b
def chan_spec.pick(up: Bool, +a: Nat, +b: Nat, +k: Nat, +n: Nat) -> Nat:
  match up:
    case True{}:
      Nat.add(a, Nat.div(Nat.mul(k, Nat.sub(b, a)), n))
    case False{}:
      Nat.add(b, Nat.div(Nat.mul(Nat.sub(n, k), Nat.sub(a, b)), n))

def chan_spec(+a: Nat, +b: Nat, +k: Nat, +n: Nat) -> Nat:
  chan_spec.pick(Nat.is_le(a, b), a, b, k, n)

# rung k (1 to n) of the ramp from lo to hi, channel by channel
def rung_spec(lo: TC.Px, hi: TC.Px, +k: Nat, +n: Nat) -> TC.Px:
  match lo hi:
    case TC.Px{lr, lg, lb} TC.Px{hr, hg, hb}:
      TC.Px{chan_spec(lr, hr, k, n), chan_spec(lg, hg, k, n), chan_spec(lb, hb, k, n)}

# LAW tui_effort_ramp_exact: rung k + 1 of an n-rung effort ramp (k below n) is, in each channel, the lower end plus floor(d * w / n), d the channel distance, w = k + 1 when the channel rises and n - k - 1 when it falls
# EXCLUDES: a ramp that is ordered and distinct but not the documented
#   one (rungs shifted by one, the low end as the first rung, the high end
#   missing, rounding up, another spacing); with tui_effort_ramp_length it
#   pins every rung
law tui_effort_ramp_exact:
  for +lo: TC.Px
  for +hi: TC.Px
  for +n: Nat
  for +k: Nat
  for lt: {Nat.is_lt(k, n) == True{} : Bool}
  {List.get(&2, TC.Px, TC.ramp(lo, hi, n), k) == Some{rung_spec(lo, hi, 1n+k, n)} : Maybe<&2, TC.Px>}

def bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# the usage band (omp getContextUsageLevel): an unknown window (0) none;
# a window of w tokens one for each of the shares 1/2, 7/10 and 9/10 of
# it that t tokens reach (w * num <= t * den)
def band_spec(+t: Nat, w: Nat) -> Nat:
  match w:
    case 0n:
      0n
    case 1n+v:
      +x = {1n+v : Nat}
      Nat.add(bit(Nat.is_le(Nat.mul(x, 1n), Nat.mul(t, 2n))), Nat.add(bit(Nat.is_le(Nat.mul(x, 7n), Nat.mul(t, 10n))), bit(Nat.is_le(Nat.mul(x, 9n), Nat.mul(t, 10n)))))

# LAW tui_usage_band_exact: the usage band of t tokens in a w-token window is 0 for an unknown window (0), else the number of the shares 1/2, 7/10 and 9/10 of the window that t reaches
# EXCLUDES: other shares (the bands' own laws hold for any ascending
#   shares in (0, 1]), a band that ignores the window or counts a share
#   it does not reach, a band for an unknown window
law tui_usage_band_exact:
  for +t: Nat
  for w: Nat
  {TC.band(t, w) == band_spec(t, w) : Nat}

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

# the k tokens a to a + k - 1, in order
def tokens_from(k: Nat, +a: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      a <> tokens_from(j, 1n+a)

# the slots of the terminal UI, in the order Rust declares them, by the
# token each paints (crates/eukhe-theme token order): the 42 ink tokens
# accent .. syntaxPunctuation (0-41), contextHigh (44), bashMode (47);
# the 9 surfaces selectedBg .. toolPanelBg (48-56); then effortLow (42),
# effortHigh (43), liftLight (45), liftDark (46), background (57)
def roles_spec() -> List<&2, Nat>:
  List.concat(&2, Nat, [tokens_from(42n, 0n), [44n, 47n], tokens_from(9n, 48n), [42n, 43n, 45n, 46n, 57n]])

# LAW tui_roles_exact: each color slot of the terminal UI is painted by its own token: the ink slots by tokens 0 to 41, then contextHigh and bashMode; the surfaces by tokens 48 to 56; then effortLow, effortHigh, liftLight, liftDark and the background
# EXCLUDES: slots that swap tokens (tui_roles_cover and the palette laws
#   hold for any order): a slot painted with another slot's color
law tui_roles_exact:
  {TC.roles() == roles_spec() : List<&2, Nat>}

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

# Reader: the requests the entry accepts, read with the wire primitives

def read_px.b(r: Nat, g: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<TC.Px>:
  match d:
    case Wr.Got{b, s}:
      Wr.Got{TC.Px{r, g, b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_px.g(r: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<TC.Px>:
  match d:
    case Wr.Got{g, s}:
      read_px.b(r, g, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_px(d: Wr.Dec<Nat>) -> Wr.Dec<TC.Px>:
  match d:
    case Wr.Got{r, s}:
      read_px.g(r, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ramp.n(lo: TC.Px, hi: TC.Px, d: Wr.Dec<Nat>) -> Wr.Dec<FTC.Req>:
  match d:
    case Wr.Got{n, s}:
      Wr.Got{FTC.QRamp{lo, hi, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_ramp.hi(lo: TC.Px, d: Wr.Dec<TC.Px>) -> Wr.Dec<FTC.Req>:
  match d:
    case Wr.Got{hi, s}:
      read_ramp.n(lo, hi, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ramp(d: Wr.Dec<TC.Px>) -> Wr.Dec<FTC.Req>:
  match d:
    case Wr.Got{lo, s}:
      read_ramp.hi(lo, read_px(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_band.w(t: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<FTC.Req>:
  match d:
    case Wr.Got{w, s}:
      Wr.Got{FTC.QBand{t, w}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_band(d: Wr.Dec<Nat>) -> Wr.Dec<FTC.Req>:
  match d:
    case Wr.Got{t, s}:
      read_band.w(t, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_req.tag(t: Nat, s: String) -> Wr.Dec<FTC.Req>:
  match t:
    case 0n:
      read_ramp(read_px(Wr.get_nat(s)))
    case 1n:
      read_band(Wr.get_nat(s))
    case 2n:
      Wr.Got{FTC.QRoles{}, s}
    case 3n+p:
      Wr.Bad{}

def read_req.go(d: Wr.Dec<Nat>) -> Wr.Dec<FTC.Req>:
  match d:
    case Wr.Got{t, s}:
      read_req.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_req.end(whole: Bool, q: FTC.Req) -> Maybe<&2, FTC.Req>:
  match whole:
    case True{}:
      Some{q}
    case False{}:
      None{}

def read_req.whole(r: Wr.Dec<FTC.Req>) -> Maybe<&2, FTC.Req>:
  match r:
    case Wr.Got{q, s}:
      read_req.end(Wr.end(s), q)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_req(s: String) -> Maybe<&2, FTC.Req>:
  read_req.whole(read_req.go(Wr.get_nat(s)))

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

# LAW tui_color_ffi_ramp_range: a ramp request with a channel above 255 or more than 255 rungs answers exactly the range error
# EXCLUDES: a ramp of a color no terminal paints, a clamped or wrapped
#   channel, a ramp too long to have distinct rungs, a slow or stopped
#   evaluation on a huge rung count
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

# LAW tui_color_ffi_malformed_exact: every input that is not exactly one request answers exactly the malformed error
# EXCLUDES: a default answer (a ramp, a band, the roles) to a request Rust
#   never sends: an unknown tag, a field missing, a number malformed
law tui_color_ffi_malformed_exact:
  for +s: String
  for no: {read_req(s) == None{} : Maybe<&2, FTC.Req>}
  {FTC.ffi(s) == malformed_err() : String}

# LAW tui_color_ffi_premises_example: the premises of the entry laws hold for real requests: a ramp of the light theme's ends is in range, one with a channel of 256 is not, and "2,x" is no request
# EXCLUDES: a vacuous tui_color_ffi_ramp, tui_color_ffi_ramp_range or
#   tui_color_ffi_malformed_exact
law tui_color_ffi_premises_example:
  {ramp_in(TC.Px{135n, 95n, 135n}, TC.Px{139n, 0n, 139n}, 3n) == True{} : Bool} &
  {ramp_in(TC.Px{0n, 0n, 0n}, TC.Px{256n, 0n, 0n}, 1n) == False{} : Bool} &
  {read_req("2,x") == None{} : Maybe<&2, FTC.Req>}

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
def tc_is_set(m: Maybe<&2, TFile.Val>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

# whether token r of the palette p has a value (a token past p has none)
def tc_set(p: List<&2, Maybe<&2, TFile.Val>>, r: Nat) -> Bool:
  match p r:
    case Nil{} _:
      False{}
    case Con{m, t} 0n:
      tc_is_set(m)
    case Con{m, t} 1n+k:
      tc_set(t, k)

# every role of rs has a value in the palette p
def tc_all(+p: List<&2, Maybe<&2, TFile.Val>>, rs: List<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, rest}:
      Bool.and(tc_set(p, r), tc_all(p, rest))

# LAW tui_resolves_spec: the roles resolve in a palette exactly when each has a value there
# EXCLUDES: a test that always holds (tui_roles_resolve made vacuous), a role
#   looked up at another token
law tui_resolves_spec:
  for +p: List<&2, Maybe<&2, TFile.Val>>
  for rs: List<&2, Nat>
  {TC.resolves(p, rs) == tc_all(p, rs) : Bool}

# LAW tui_resolves_example: anchors: an unset token does not resolve, a set one does, a token
# past the palette does not
# EXCLUDES: a reading of tui_resolves_spec the human did not mean
law tui_resolves_example:
  {[TC.resolves([None{}], [0n]), TC.resolves([Some{TFile.Dflt{}}], [0n]), TC.resolves([Some{TFile.Dflt{}}], [1n])] == [False{}, True{}, False{}] : List<&2, Bool>}

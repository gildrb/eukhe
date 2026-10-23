# eukhe: the laws of area tui_color

import Base
import ../bend/theme/bundled.bend as TBundled
import ../bend/tui_color.bend as TC

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
# length, any token count and any window. The bridge test
# crates/eukhe-tui/src/theme/bridge.rs checks that the Rust ramp, the Rust
# bands and the Rust roles equal the model.

# LAW: the effort ramp has one rung for each level the model offers
law tui_effort_ramp_length:
  for lo: TC.Px
  for hi: TC.Px
  for n: Nat
  {List.length(&2, TC.Px, TC.ramp(lo, hi, n)) == n : Nat}

# LAW: for any ladder length, along the effort ramp every channel moves
# from the low end toward the high end, never back
law tui_effort_ramp_ordered:
  for lo: TC.Px
  for hi: TC.Px
  for n: Nat
  {TC.ordered(lo, hi, TC.ramp(lo, hi, n)) == True{} : Bool}

# LAW: for any ladder length up to the widest channel distance of the
# ends, no two rungs of the effort ramp have the same color
law tui_effort_ramp_distinct:
  for lo: TC.Px
  for hi: TC.Px
  for n: Nat
  for fits: {Nat.is_le(n, TC.span(lo, hi)) == True{} : Bool}
  {TC.distinct(TC.ramp(lo, hi, n)) == True{} : Bool}

# LAW: in every shipped theme, no two rungs of the effort ramp have the
# same color, for any ladder of the level vocabulary
law tui_effort_shipped_distinct:
  for s: TBundled.Shipped
  for n: Nat
  for fits: {Nat.is_le(n, TC.ladder.max()) == True{} : Bool}
  {TC.distinct(TC.ramp(TC.shipped.lo(s), TC.shipped.hi(s), n)) == True{} : Bool}

# LAW: every usage band is a fraction of the window above zero and at
# most one, and each band is above the band before it
law tui_usage_bands_ascend:
  {TC.ascend(TC.bands()) == True{} : Bool}

# LAW: more tokens in the same window never give a lower usage band
law tui_usage_band_monotone:
  for t: Nat
  for e: Nat
  for w: Nat
  {Nat.is_le(TC.band(t, w), TC.band(Nat.add(t, e), w)) == True{} : Bool}

# LAW: the usage band depends only on the fraction of the window in use:
# the same fraction of a window k times as large gives the same band
law tui_usage_band_fraction:
  for k: Nat
  for t: Nat
  for w: Nat
  {TC.band(Nat.mul(1n+k, t), Nat.mul(1n+k, w)) == TC.band(t, w) : Nat}

# LAW: tokens at or past the window reach what the full window reaches,
# so the caller may cap the tokens at the window (and at any cap at or
# above the window) without changing the band
# EXCLUDES: a band that changes past the full window (an overflow, a
#   wrap, a fraction above one read as more)
law tui_usage_band_full:
  for +t: Nat
  for +w: Nat
  for +past: {Nat.is_le(w, t) == True{} : Bool}
  {TC.band(t, w) == TC.band(w, w) : Nat}

# LAW: every color role of the terminal UI paints a color in every
# shipped theme
law tui_roles_shipped:
  for s: TBundled.Shipped
  {TC.paints(TBundled.table(s), TC.roles()) == True{} : Bool}

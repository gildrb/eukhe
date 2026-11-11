# eukhe: the laws of area effort, section depth: reasoning depth (S10), the model in bend/effort.bend

import Base
import ../../bend/effort.bend as Ef

# (S10) Reasoning depth
# ---------------------
# The functions of bend/effort.bend. Every input is free: any model,
# reasoning or not, with any thinking-level map (each entry missing, null
# or a wire string); any level; any stored level and default; any model
# switches, sets and cycle steps, in any order.
#
# Shipped or a model. The entry bend/ffi_effort.bend answers Ef.offered,
# Ef.clamp and Ef.cycle of the model its facts give (laws/effort/ladder.bend
# core_effort_offered, core_effort_clamp, core_effort_cycle): sections 1-3
# below are about shipped code. Section 4, the session (Ef.open, act, run,
# sent, shown), is NOT compiled into the core (crates/eukhe-bend/c/core.c
# has no entry for it) and no Rust code calls it: the session that ships
# is Rust's own (eukhe-daemon rpc/model_commands.rs, eukhe-tui
# session_ui/model_picker.rs), which these laws do not check. Section 4
# states the session rules for the Bend model only.
#
# Requirements (the header of bend/effort.bend; crates/eukhe-ai
# models/ladder.rs; omp c28b3e3 where they are silent or differ):
# A1 The ladder: off, minimal, low, medium, high, xhigh, max, in that order
#    (effort_rank; omp THINKING_EFFORTS, off below every effort).
# A2 A reasoning model offers a level whose map entry is a wire string.
# A3 A reasoning model offers a level below xhigh that its map has no
#    entry for.
# A4 A reasoning model never offers a level whose map entry is null.
# A5 A model offers xhigh or max only with a wire string for it.
# A6 The offered levels are in ladder order, each once.
# A7 A model without reasoning offers off only. Dead for the shipped entry:
#    the facts always give a reasoning Ef.Mdl (bend/infer.bend lad.model);
#    a model without reasoning offers its plain default ladder there
#    (laws/effort/ladder.bend quirk_ladder_plain_exact). No law here.
# A8 The clamp, as eukhe v0.10.67 clamps (tag eukhe-v0.10.67, f58acb642:
#    bend/effort.bend header rule 2, crates/eukhe-ai models/ladder.rs
#    clamp and its vectors): a level the model offers stays; another goes
#    to the lowest offered level above it, else to the highest offered
#    level below it (off included), else to off. omp's agent clamps down
#    first instead (omp c28b3e3 packages/catalog/src/model-thinking.ts:42-87);
#    eukhe keeps v0.10.67's order on purpose (the commit that states this
#    law lists the divergence, model by model).
# A9 The clamp of any level for a model that offers none is off.
# A10 The clamp lands on an offered level; a second clamp changes nothing.
# A11 A cycle step gives a level exactly when two or more are offered;
#    else it gives none and nothing changes (Rust: `null`).
# A12 A cycle step starts at the clamp of the current level.
# A13 Forward gives the next offered level and wraps from the last to the
#    first; backward the one before, wrapping from the first to the last;
#    each undoes the other.
# A14 Open: the model kept, the stored level, else the default, fitted
#    (clamped with a catalog model, A8/A9; unchanged without one).
# A15 A switch takes the new model and fits the stored level to it; no
#    stored level stays none.
# A16 A set stores the requested level fitted.
# A17 A cycle step with a catalog model stores the level the step gives,
#    the stored level unchanged when it gives none; without a catalog
#    model or a stored level it changes nothing.
# A18 A run applies its actions one by one, in order.
# A19 The runtime sends the stored level, else off, fitted; after open the
#    session stores what it sends.
# A20 The display shows `default` while no level is stored (only a set
#    stores one), else the stored level fitted; after open it shows what
#    the session sends.
#
# Trusted (spec helpers call them): Ef.has (membership), Ef.entry (a map's
# entry of a level), Ef.offered, Ef.cycle where a law relates another
# function to them, Maybe.default, List.length, List.append.

# Terms
# -----

# a level's place on the ladder: off 0, minimal 1, low 2, medium 3, high 4,
# xhigh 5, max 6 (the order bend/effort.bend's header and omp's
# THINKING_EFFORTS list, off below every effort)
def effort_rank(l: Ef.Lv) -> Nat:
  match l:
    case Ef.Off{}:
      0n
    case Ef.Minimal{}:
      1n
    case Ef.Low{}:
      2n
    case Ef.Medium{}:
      3n
    case Ef.High{}:
      4n
    case Ef.Xhigh{}:
      5n
    case Ef.Max{}:
      6n

# x is a level the clamp of l passes over before it lands on k: none when
# k is l; l and the levels between when k is above l; every level above k
# when k is below l (l, the levels above l, then those down to k)
# (a, b, c: the ranks of l, k, x)
def effort_skipped.at(same: Bool, down: Bool, +a: Nat, +b: Nat, +c: Nat) -> Bool:
  match same:
    case True{}:
      False{}
    case False{}:
      match down:
        case True{}:
          Nat.is_lt(b, c)
        case False{}:
          Bool.and(Nat.is_le(a, c), Nat.is_lt(c, b))

def effort_skipped(+l: Ef.Lv, +k: Ef.Lv, x: Ef.Lv) -> Bool:
  effort_skipped.at(Nat.is_eq(effort_rank(l), effort_rank(k)), Nat.is_lt(effort_rank(k), effort_rank(l)), effort_rank(l), effort_rank(k), effort_rank(x))

# no level of xs is passed over on the way from l to k
def effort_clear(xs: List<&2, Ef.Lv>, +l: Ef.Lv, +k: Ef.Lv) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Bool.not(effort_skipped(l, k, x)), effort_clear(rest, l, k))

# k is where the clamp of l lands among the offered levels xs (eukhe
# v0.10.67's order, A8): k is offered, and no offered level is passed
# over: k is l itself, else the lowest offered level above l, else the
# highest offered level below l
def effort_lands(+xs: List<&2, Ef.Lv>, +l: Ef.Lv, +k: Ef.Lv) -> Bool:
  Bool.and(Ef.has(xs, k), effort_clear(xs, l, k))

def effort_fits.of(+xs: List<&2, Ef.Lv>, +l: Ef.Lv, +k: Ef.Lv) -> Bool:
  Bool.or(effort_lands(xs, l, k), Bool.and(Nat.is_eq(List.length(&2, Ef.Lv, xs), 0n), Nat.is_eq(effort_rank(k), 0n)))

# A14-A17: k is l fitted to the catalog model mo: with a model, where its
# clamp lands (A8), or off when it offers no level (A9); without one, l
def effort_fits(mo: Maybe<&2, Ef.Mdl>, +l: Ef.Lv, +k: Ef.Lv) -> Bool:
  match mo:
    case None{}:
      Nat.is_eq(effort_rank(l), effort_rank(k))
    case Some{m}:
      effort_fits.of(Ef.offered(m), l, k)

# A15: r is the stored level st fitted to mo: none for none
def effort_fits_m(mo: Maybe<&2, Ef.Mdl>, st: Maybe<&2, Ef.Lv>, r: Maybe<&2, Ef.Lv>) -> Bool:
  match st:
    case None{}:
      match r:
        case None{}:
          True{}
        case Some{k}:
          False{}
    case Some{l}:
      match r:
        case None{}:
          False{}
        case Some{k}:
          effort_fits(mo, l, k)

# A20: no action of acts is a set
def effort_no_set(acts: List<&2, Ef.Act>) -> Bool:
  match acts:
    case Nil{}:
      True{}
    case a <> rest:
      match a:
        case Ef.Switch{m}:
          effort_no_set(rest)
        case Ef.SetLevel{l}:
          False{}
        case Ef.Step{d}:
          effort_no_set(rest)

# Laws
# ----

# 1. The offered levels
# ---------------------

# LAW effort_offered_wired (A2): a reasoning model offers every level its map gives a wire
# string, xhigh and max among them
# EXCLUDES: a wired level dropped; a filter that reads another level's entry
law effort_offered_wired:
  for +map: Ef.LvMap
  for +l: Ef.Lv
  for wire: {Ef.entry(l, map) == Ef.Wire{} : Ef.Ent}
  {Ef.has(Ef.offered(Ef.Mdl{True{}, map}), l) == True{} : Bool}

# LAW effort_offered_missing (A3): a reasoning model offers every level below xhigh (rank
# under 5) that its map has no entry for
# EXCLUDES: a missing entry read as null (a map that names some levels drops
#   the others); a missing level below xhigh dropped
law effort_offered_missing:
  for +map: Ef.LvMap
  for +l: Ef.Lv
  for below: {Nat.is_lt(effort_rank(l), 5n) == True{} : Bool}
  for none: {Ef.entry(l, map) == Ef.Missing{} : Ef.Ent}
  {Ef.has(Ef.offered(Ef.Mdl{True{}, map}), l) == True{} : Bool}

# LAW effort_offered_null (A4): a reasoning model never offers a level with a null entry
law effort_offered_null:
  for +map: Ef.LvMap
  for +l: Ef.Lv
  for null: {Ef.entry(l, map) == Ef.Null{} : Ef.Ent}
  {Ef.has(Ef.offered(Ef.Mdl{True{}, map}), l) == False{} : Bool}

# LAW effort_offered_ext (A5): a model, reasoning or not, offers xhigh or max (rank 5 or
# more) only when its map gives that level a wire string
# EXCLUDES: xhigh or max offered for a missing or null entry
law effort_offered_ext:
  for r: Bool
  for +map: Ef.LvMap
  for +l: Ef.Lv
  for top: {Nat.is_le(5n, effort_rank(l)) == True{} : Bool}
  for in: {Ef.has(Ef.offered(Ef.Mdl{r, map}), l) == True{} : Bool}
  {Ef.entry(l, map) == Ef.Wire{} : Ef.Ent}

# LAW effort_offered_asc (A6): the offered levels are strictly ascending in ladder order: no
# level comes twice
law effort_offered_asc:
  for m: Ef.Mdl
  {Ef.asc(Ef.offered(m)) == True{} : Bool}

# 2. The clamp
# ------------

# LAW effort_clamp_up_first (A8): the clamp of a level l lands on k whenever k is offered and
# no offered level is passed over on the way (effort_lands): l itself when
# offered; else the lowest offered level above l; else the highest offered
# level below l, off included. The order is eukhe v0.10.67's (tag
# eukhe-v0.10.67); omp's agent clamps down first, a divergence kept on
# purpose (no wire regression against v0.10.67 on any catalog model)
# EXCLUDES: a clamp that goes down before up (high on off, low, medium,
#   xhigh giving medium), that skips the nearest offered level above, that
#   lands on a level not offered, or that moves an offered level
law effort_clamp_up_first:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for +k: Ef.Lv
  for lands: {effort_lands(Ef.offered(m), l, k) == True{} : Bool}
  {Ef.clamp(m, l) == k : Ef.Lv}

# LAW effort_clamp_v0_10_67_example (A8): anchor and witness: the Kimi K3 ladder (low, high,
# max; here with off) clamps xhigh to max, medium to high and minimal to
# low, as eukhe v0.10.67 does on its catalog (fireworks
# accounts/fireworks/models/kimi-k3: medium -> high, xhigh -> max)
# EXCLUDES: a vacuous effort_clamp_up_first; a down-first clamp (xhigh to
#   high, medium to low)
law effort_clamp_v0_10_67_example:
  {[effort_lands(Ef.offered(Ef.Mdl{True{}, Ef.LvMap{Ef.Wire{}, Ef.Null{}, Ef.Wire{}, Ef.Null{}, Ef.Wire{}, Ef.Null{}, Ef.Wire{}}}), Ef.Xhigh{}, Ef.Max{}), effort_lands(Ef.offered(Ef.Mdl{True{}, Ef.LvMap{Ef.Wire{}, Ef.Null{}, Ef.Wire{}, Ef.Null{}, Ef.Wire{}, Ef.Null{}, Ef.Wire{}}}), Ef.Medium{}, Ef.High{})] == [True{}, True{}] : List<&2, Bool>} & {[Ef.clamp(Ef.Mdl{True{}, Ef.LvMap{Ef.Wire{}, Ef.Null{}, Ef.Wire{}, Ef.Null{}, Ef.Wire{}, Ef.Null{}, Ef.Wire{}}}, Ef.Xhigh{}), Ef.clamp(Ef.Mdl{True{}, Ef.LvMap{Ef.Wire{}, Ef.Null{}, Ef.Wire{}, Ef.Null{}, Ef.Wire{}, Ef.Null{}, Ef.Wire{}}}, Ef.Medium{}), Ef.clamp(Ef.Mdl{True{}, Ef.LvMap{Ef.Wire{}, Ef.Null{}, Ef.Wire{}, Ef.Null{}, Ef.Wire{}, Ef.Null{}, Ef.Wire{}}}, Ef.Minimal{})] == [Ef.Max{}, Ef.High{}, Ef.Low{}] : List<&2, Ef.Lv>}

# LAW effort_clamp_none (A9): a model that offers no level clamps every level to off
# EXCLUDES: a level kept, or another default, when nothing is offered
law effort_clamp_none:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for none: {Ef.offered(m) == [] : List<&2, Ef.Lv>}
  {Ef.clamp(m, l) == Ef.Off{} : Ef.Lv}

# LAW effort_clamp_offered (A10): when the model offers a level, the clamp of any level is
# an offered level
law effort_clamp_offered:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for ne: {Ef.empty(Ef.offered(m)) == False{} : Bool}
  {Ef.has(Ef.offered(m), Ef.clamp(m, l)) == True{} : Bool}

# LAW effort_clamp_idem (A10): a second clamp changes nothing, also when the model offers no level
law effort_clamp_idem:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  {Ef.clamp(m, Ef.clamp(m, l)) == Ef.clamp(m, l) : Ef.Lv}

# 3. The cycle
# ------------

# LAW effort_cycle_moves (A11): a cycle step gives a level exactly when the model offers two
# or more levels (a count, List.length, of 2 or more); else it gives none
# EXCLUDES: a step that moves on a ladder of one level, or that gives none
#   (nothing changes) on a ladder of two or more
law effort_cycle_moves:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for +d: Ef.Dir
  {Maybe.is_some(&2, Ef.Lv, Ef.cycle(m, l, d)) == Nat.is_le(2n, List.length(&2, Ef.Lv, Ef.offered(m))) : Bool}

# LAW effort_cycle_from_clamp (A12): a cycle step from any level is the step from the level
# it clamps to
# EXCLUDES: a step from a level the model does not offer that starts
#   anywhere else (the first offered level, off)
law effort_cycle_from_clamp:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for +d: Ef.Dir
  {Ef.cycle(m, l, d) == Ef.cycle(m, Ef.clamp(m, l), d) : Maybe<&2, Ef.Lv>}

# LAW effort_cycle_next (A13): forward from an offered level gives the next offered level
law effort_cycle_next:
  for +m: Ef.Mdl
  for +pre: List<&2, Ef.Lv>
  for +a: Ef.Lv
  for +b: Ef.Lv
  for +post: List<&2, Ef.Lv>
  for +split: {Ef.offered(m) == List.append(&2, Ef.Lv, pre, a <> b <> post) : List<&2, Ef.Lv>}
  {Ef.cycle(m, a, Ef.Forward{}) == Some{b} : Maybe<&2, Ef.Lv>}

# LAW effort_cycle_wrap (A13): forward from the last offered level wraps to the first
law effort_cycle_wrap:
  for +m: Ef.Mdl
  for +h: Ef.Lv
  for +pre: List<&2, Ef.Lv>
  for +z: Ef.Lv
  for +split: {Ef.offered(m) == List.append(&2, Ef.Lv, h <> pre, [z]) : List<&2, Ef.Lv>}
  {Ef.cycle(m, z, Ef.Forward{}) == Some{h} : Maybe<&2, Ef.Lv>}

# LAW effort_cycle_prev (A13): backward from an offered level gives the offered level before it
law effort_cycle_prev:
  for +m: Ef.Mdl
  for +pre: List<&2, Ef.Lv>
  for +a: Ef.Lv
  for +b: Ef.Lv
  for +post: List<&2, Ef.Lv>
  for +split: {Ef.offered(m) == List.append(&2, Ef.Lv, pre, a <> b <> post) : List<&2, Ef.Lv>}
  {Ef.cycle(m, b, Ef.Backward{}) == Some{a} : Maybe<&2, Ef.Lv>}

# LAW effort_cycle_wrap_back (A13): backward from the first offered level wraps to the last
law effort_cycle_wrap_back:
  for +m: Ef.Mdl
  for +h: Ef.Lv
  for +pre: List<&2, Ef.Lv>
  for +z: Ef.Lv
  for split: {Ef.offered(m) == List.append(&2, Ef.Lv, h <> pre, [z]) : List<&2, Ef.Lv>}
  {Ef.cycle(m, h, Ef.Backward{}) == Some{z} : Maybe<&2, Ef.Lv>}

# LAW effort_cycle_inverse (A13): a backward step undoes a forward step from an offered level
law effort_cycle_inverse:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for in: {Ef.has(Ef.offered(m), l) == True{} : Bool}
  {Ef.turn(m, Ef.turn(m, l, Ef.Forward{}), Ef.Backward{}) == l : Ef.Lv}

# LAW effort_cycle_inverse_back (A13): a forward step undoes a backward step from an offered level
law effort_cycle_inverse_back:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for in: {Ef.has(Ef.offered(m), l) == True{} : Bool}
  {Ef.turn(m, Ef.turn(m, l, Ef.Backward{}), Ef.Forward{}) == l : Ef.Lv}

# 4. The session (a model, not compiled into the core)
# ----------------------------------------------------

# LAW effort_open_fits (A14): open keeps the model and stores the stored level, else the
# default, fitted to the model (effort_fits)
# EXCLUDES: the default over a stored level, or off for no stored level; an
#   unfitted level, or one fitted to another model; the model dropped
law effort_open_fits:
  for +mo: Maybe<&2, Ef.Mdl>
  for +st: Maybe<&2, Ef.Lv>
  for +dflt: Ef.Lv
  for +k: Ef.Lv
  for fit: {effort_fits(mo, Maybe.default(&2, Ef.Lv, st, dflt), k) == True{} : Bool}
  {Ef.open(Ef.Sess{mo, st}, dflt) == Ef.Sess{mo, Some{k}} : Ef.Sess}

# LAW effort_switch_fits (A15): a switch to the model m takes m and fits the stored level to
# m; no stored level stays none
# EXCLUDES: a switch that keeps the old model, resets the level, keeps it
#   unfitted, or stores a level where none was stored
law effort_switch_fits:
  for +m: Ef.Mdl
  for +mo: Maybe<&2, Ef.Mdl>
  for +st: Maybe<&2, Ef.Lv>
  for +r: Maybe<&2, Ef.Lv>
  for fit: {effort_fits_m(Some{m}, st, r) == True{} : Bool}
  {Ef.act(Ef.Switch{m}, Ef.Sess{mo, st}) == Ef.Sess{Some{m}, r} : Ef.Sess}

# LAW effort_set_fits (A16): a set stores the requested level fitted to the model, whatever
# was stored, and keeps the model
# EXCLUDES: a set that keeps the old level, or stores the request unfitted
law effort_set_fits:
  for +mo: Maybe<&2, Ef.Mdl>
  for st: Maybe<&2, Ef.Lv>
  for +k: Ef.Lv
  for +j: Ef.Lv
  for fit: {effort_fits(mo, k, j) == True{} : Bool}
  {Ef.act(Ef.SetLevel{k}, Ef.Sess{mo, st}) == Ef.Sess{mo, Some{j}} : Ef.Sess}

# LAW effort_step_turns (A17): a cycle step of a stored level l with a catalog model m stores
# the level the step gives (Ef.cycle, pinned by section 3), l unchanged when
# it gives none
# EXCLUDES: a step that stores another level than the cycle gives, moves
#   the other way, or resets the level when nothing changes
law effort_step_turns:
  for +m: Ef.Mdl
  for +l: Ef.Lv
  for +d: Ef.Dir
  {Ef.act(Ef.Step{d}, Ef.Sess{Some{m}, Some{l}}) == Ef.Sess{Some{m}, Some{Maybe.default(&2, Ef.Lv, Ef.cycle(m, l, d), l)}} : Ef.Sess}

# LAW effort_step_still (A17): a cycle step without a catalog model or without a stored
# level changes nothing
# EXCLUDES: a step that invents a level, or moves one with no model
law effort_step_still:
  for +mo: Maybe<&2, Ef.Mdl>
  for +st: Maybe<&2, Ef.Lv>
  for +d: Ef.Dir
  for idle: {Bool.or(Maybe.is_none(&2, Ef.Mdl, mo), Maybe.is_none(&2, Ef.Lv, st)) == True{} : Bool}
  {Ef.act(Ef.Step{d}, Ef.Sess{mo, st}) == Ef.Sess{mo, st} : Ef.Sess}

# LAW effort_run_in_order (A18): a run of one action is that action, and a run of xs then
# ys is the run of ys after the run of xs: the actions apply one by one, in
# order
# EXCLUDES: a run that drops, repeats or reorders an action
law effort_run_in_order:
  for +a: Ef.Act
  for +xs: List<&2, Ef.Act>
  for +ys: List<&2, Ef.Act>
  for +s: Ef.Sess
  {Ef.run([a], s) == Ef.act(a, s) : Ef.Sess} & {Ef.run(List.append(&2, Ef.Act, xs, ys), s) == Ef.run(ys, Ef.run(xs, s)) : Ef.Sess}

# LAW effort_sent_fits (A19): the runtime sends the stored level, else off, fitted to the
# model
# EXCLUDES: the default instead of off; an unfitted level
law effort_sent_fits:
  for +mo: Maybe<&2, Ef.Mdl>
  for +st: Maybe<&2, Ef.Lv>
  for +k: Ef.Lv
  for fit: {effort_fits(mo, Maybe.default(&2, Ef.Lv, st, Ef.Off{}), k) == True{} : Bool}
  {Ef.sent(Ef.Sess{mo, st}) == k : Ef.Lv}

# LAW effort_shown_fits (A20): a session with a stored level shows it fitted to the model
# EXCLUDES: the unfitted level shown; `default` shown for a stored level
law effort_shown_fits:
  for +mo: Maybe<&2, Ef.Mdl>
  for +l: Ef.Lv
  for +k: Ef.Lv
  for fit: {effort_fits(mo, l, k) == True{} : Bool}
  {Ef.shown(Ef.Sess{mo, Some{l}}) == Ef.Level{k} : Ef.Shown}

# LAW effort_unset_stays (A15, A17, A20): a session with no stored level shows `default`,
# never off, after any run of switches and cycle steps: only a set stores a
# level
# EXCLUDES: off shown for no stored level; a switch or a step that stores a
#   level
law effort_unset_stays:
  for +mo: Maybe<&2, Ef.Mdl>
  for +acts: List<&2, Ef.Act>
  for noset: {effort_no_set(acts) == True{} : Bool}
  {Ef.shown(Ef.run(acts, Ef.Sess{mo, None{}})) == Ef.Default{} : Ef.Shown}

# LAW effort_settle_offered (A14): open settles the stored level on an offered level when the model
# offers one
law effort_settle_offered:
  for +m: Ef.Mdl
  for +st: Maybe<&2, Ef.Lv>
  for +dflt: Ef.Lv
  for +k: Ef.Lv
  for ne: {Ef.empty(Ef.offered(m)) == False{} : Bool}
  for settled: {Ef.Sess.stored(Ef.open(Ef.Sess{Some{m}, st}, dflt)) == Some{k} : Maybe<&2, Ef.Lv>}
  {Ef.has(Ef.offered(m), k) == True{} : Bool}

# LAW effort_stored_is_sent (A19): after open and any actions, the session stores the level it sends
law effort_stored_is_sent:
  for +s: Ef.Sess
  for +dflt: Ef.Lv
  for +acts: List<&2, Ef.Act>
  {Ef.Sess.stored(Ef.run(acts, Ef.open(s, dflt))) == Some{Ef.sent(Ef.run(acts, Ef.open(s, dflt)))} : Maybe<&2, Ef.Lv>}

# LAW effort_shown_is_sent (A20): after open and any actions, the display shows the level the
# session sends
law effort_shown_is_sent:
  for +s: Ef.Sess
  for +dflt: Ef.Lv
  for +acts: List<&2, Ef.Act>
  {Ef.shown(Ef.run(acts, Ef.open(s, dflt))) == Ef.Level{Ef.sent(Ef.run(acts, Ef.open(s, dflt)))} : Ef.Shown}

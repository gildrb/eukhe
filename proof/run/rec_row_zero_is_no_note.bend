# eukhe: the proof of LAW rec_row_zero_is_no_note
#
# PROOF: a row of 0 counts no note of any recovery, as no note does; the
# record a help is read from then differs only in the note's recovery,
# which no help reads (rz.*: by cases on the recovery's tests). By cases on
# the stuck reply and the note.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/recover.bend as RunRecover

def rz.think(shrink: Bool, under: Bool, lowers: Bool, +same: Nat, k: RnRecovery.Rk) -> {RnDecision.Help.of(RnRecovery.rec.think(shrink, under, lowers, 0n, same, 0n, RnRecovery.Rec{k, 0n, same, 0n})) == RnDecision.Help.of(RnRecovery.rec.think(shrink, under, lowers, 0n, same, 0n, RnRecovery.Rec{RnRecovery.Free{}, 0n, same, 0n})) : RnDecision.Help}:
  match shrink:
    case True{}:
      {==}
    case False{}:
      match under:
        case True{}:
          {==}
        case False{}:
          match lowers:
            case True{}:
              {==}
            case False{}:
              {==}

def rz.leak(under: Bool, +same: Nat, k: RnRecovery.Rk) -> {RnDecision.Help.of(RnRecovery.rec.leak(under, 0n, same, 0n, RnRecovery.Rec{k, 0n, same, 0n})) == RnDecision.Help.of(RnRecovery.rec.leak(under, 0n, same, 0n, RnRecovery.Rec{RnRecovery.Free{}, 0n, same, 0n})) : RnDecision.Help}:
  match under:
    case True{}:
      {==}
    case False{}:
      {==}

def rz.ran(fresh: Bool, under: Bool, kept: Bool, +m: Nat, +h: Nat, +same: Nat, k: RnRecovery.Rk) -> {RnDecision.Help.of(RnRecovery.rec.ran(fresh, under, kept, m, h, 0n, same, 0n, RnRecovery.Rec{k, 0n, same, 0n})) == RnDecision.Help.of(RnRecovery.rec.ran(fresh, under, kept, m, h, 0n, same, 0n, RnRecovery.Rec{RnRecovery.Free{}, 0n, same, 0n})) : RnDecision.Help}:
  match fresh:
    case True{}:
      {==}
    case False{}:
      match under:
        case True{}:
          {==}
        case False{}:
          {==}

def RunRecover.rec_row_zero_is_no_note(rc, s, k):
  match s:
    case RnDecision.Thought{w, c, p, o, cuttable, lower}:
      match k:
        case RnRecovery.Free{}:
          {==}
        case RnRecovery.Longs{}:
          rz.think(RnRecovery.full(w, c, p, o, cuttable), RnRecovery.below(0n, RnRecovery.RCfg.long(rc)), Bool.and(lower, Nat.is_eq(0n, RnRecovery.RCfg.long(rc))), 0n, RnRecovery.Longs{})
        case RnRecovery.Leaks{}:
          rz.think(RnRecovery.full(w, c, p, o, cuttable), RnRecovery.below(0n, RnRecovery.RCfg.long(rc)), Bool.and(lower, Nat.is_eq(0n, RnRecovery.RCfg.long(rc))), 0n, RnRecovery.Leaks{})
        case RnRecovery.Loops{}:
          rz.think(RnRecovery.full(w, c, p, o, cuttable), RnRecovery.below(0n, RnRecovery.RCfg.long(rc)), Bool.and(lower, Nat.is_eq(0n, RnRecovery.RCfg.long(rc))), 0n, RnRecovery.Loops{})
        case RnRecovery.Empties{}:
          rz.think(RnRecovery.full(w, c, p, o, cuttable), RnRecovery.below(0n, RnRecovery.RCfg.long(rc)), Bool.and(lower, Nat.is_eq(0n, RnRecovery.RCfg.long(rc))), 0n, RnRecovery.Empties{})
    case RnDecision.Leaked{}:
      match k:
        case RnRecovery.Free{}:
          {==}
        case RnRecovery.Longs{}:
          rz.leak(RnRecovery.below(0n, RnRecovery.RCfg.leak(rc)), 0n, RnRecovery.Longs{})
        case RnRecovery.Leaks{}:
          rz.leak(RnRecovery.below(0n, RnRecovery.RCfg.leak(rc)), 0n, RnRecovery.Leaks{})
        case RnRecovery.Loops{}:
          rz.leak(RnRecovery.below(0n, RnRecovery.RCfg.leak(rc)), 0n, RnRecovery.Loops{})
        case RnRecovery.Empties{}:
          rz.leak(RnRecovery.below(0n, RnRecovery.RCfg.leak(rc)), 0n, RnRecovery.Empties{})
    case RnDecision.Repeats{before}:
      match k:
        case RnRecovery.Free{}:
          {==}
        case RnRecovery.Longs{}:
          rz.ran(RnRecovery.below(RnRecovery.again(before, 0n, 0n), RnRecovery.RCfg.repeat(rc)), RnRecovery.below(0n, RnRecovery.RCfg.redirect(rc)), True{}, RnRecovery.again(before, 0n, 0n), 0n, before, RnRecovery.Longs{})
        case RnRecovery.Leaks{}:
          rz.ran(RnRecovery.below(RnRecovery.again(before, 0n, 0n), RnRecovery.RCfg.repeat(rc)), RnRecovery.below(0n, RnRecovery.RCfg.redirect(rc)), True{}, RnRecovery.again(before, 0n, 0n), 0n, before, RnRecovery.Leaks{})
        case RnRecovery.Loops{}:
          rz.ran(RnRecovery.below(RnRecovery.again(before, 0n, 0n), RnRecovery.RCfg.repeat(rc)), RnRecovery.below(0n, RnRecovery.RCfg.redirect(rc)), True{}, RnRecovery.again(before, 0n, 0n), 0n, before, RnRecovery.Loops{})
        case RnRecovery.Empties{}:
          rz.ran(RnRecovery.below(RnRecovery.again(before, 0n, 0n), RnRecovery.RCfg.repeat(rc)), RnRecovery.below(0n, RnRecovery.RCfg.redirect(rc)), True{}, RnRecovery.again(before, 0n, 0n), 0n, before, RnRecovery.Empties{})
    case RnDecision.Emptied{}:
      match k:
        case RnRecovery.Free{}:
          {==}
        case RnRecovery.Longs{}:
          {==}
        case RnRecovery.Leaks{}:
          {==}
        case RnRecovery.Loops{}:
          {==}
        case RnRecovery.Empties{}:
          {==}

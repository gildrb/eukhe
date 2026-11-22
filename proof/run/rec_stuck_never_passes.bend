# eukhe: the proof of LAW rec_stuck_never_passes
#
# PROOF: by cases on the tests each recovery reads: every arm of rec.leak,
# rec.ran, rec.empty and rec.think is a call run, a retry with a note, a
# compaction, a lower level or the failed run, none a pass.

import Base
import ../../bend/stop.bend as Stop
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover

def np.leak(u: Bool, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec) -> {RunRecover.passes(RnRecovery.Dec.act(RnRecovery.rec.leak(u, n, same, last, r))) == False{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def np.empty(u: Bool, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec) -> {RunRecover.passes(RnRecovery.Dec.act(RnRecovery.rec.empty(u, n, same, last, r))) == False{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def np.ran(fresh: Bool, u: Bool, -kept: Bool, -m: Nat, -h: Nat, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec) -> {RunRecover.passes(RnRecovery.Dec.act(RnRecovery.rec.ran(fresh, u, kept, m, h, n, same, last, r))) == False{} : Bool}:
  match fresh u:
    case True{} u:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def np.think(s: Bool, u: Bool, l: Bool, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec) -> {RunRecover.passes(RnRecovery.Dec.act(RnRecovery.rec.think(s, u, l, n, same, last, r))) == False{} : Bool}:
  match s:
    case True{}:
      {==}
    case False{}:
      match u:
        case True{}:
          {==}
        case False{}:
          match l:
            case True{}:
              {==}
            case False{}:
              {==}

def np.calls(+rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, +h: Nat, kept: Bool) -> {RunRecover.passes(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last}))) == False{} : Bool}:
  np.ran(RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)), RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last})

def np.leaked(+rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, rebuilt: Bool, +h: Nat, kept: Bool) -> {RunRecover.passes(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Leak{rebuilt, h, kept}, RnRecovery.Rec{k, row, same, last}))) == False{} : Bool}:
  match rebuilt:
    case True{}:
      np.calls(rc, k, row, same, last, h, kept)
    case False{}:
      np.leak(RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)), RnRecovery.Rk.leaks(k, row), same, last, RnRecovery.Rec{k, row, same, last})

def RunRecover.rec_stuck_never_passes(rc, k, row, same, last, rebuilt, h, kept, shrink, lower):
  (np.leaked(rc, k, row, same, last, rebuilt, h, kept), (np.calls(rc, k, row, same, last, h, kept), (np.empty(RnRecovery.below(RnRecovery.Rk.empties(k, row), Stop.empty_cap()), RnRecovery.Rk.empties(k, row), same, last, RnRecovery.Rec{k, row, same, last}), np.think(shrink, RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)), Bool.and(lower, Nat.is_eq(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc))), RnRecovery.Rk.longs(k, row), same, last, RnRecovery.Rec{k, row, same, last}))))

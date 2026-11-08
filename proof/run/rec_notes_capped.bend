# eukhe: the proof of LAW rec_notes_capped

import Base
import ../../bend/stop.bend as Stop
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/model.bend as Run
import ./base.bend as LA

# Every recovery stops at its cap
# -------------------------------
# Each lemma takes a cap test u with its equation e, as a match needs a
# parameter.

# n < m, so n < 1 + m
def below_up(+n: Nat, +m: Nat, h: {RnRecovery.below(n, m) == True{} : Bool}) -> {RnRecovery.below(n, 1n+m) == True{} : Bool}:
  match n m:
    case 0n 0n:
      LA.rk.absurd({RnRecovery.below(0n, 1n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LA.rk.absurd({RnRecovery.below(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      below_up(p, q, h)

# n = m, so n < 1 + m
def below_eq(+n: Nat, +m: Nat, h: {Nat.is_eq(n, m) == True{} : Bool}) -> {RnRecovery.below(n, 1n+m) == True{} : Bool}:
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LA.rk.absurd({RnRecovery.below(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      below_eq(p, q, h)

# a length note under the cap makes a row of at most the cap, within the
# cap of the length notes (one more for the last rung of rec.think)
def cap_long(+rc: RnRecovery.RCfg, u: Bool, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, e: {RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)) == u : Bool}, ok: {RnRecovery.Rk.capped(rc, k, row) == True{} : Bool}) -> {RnRecovery.Rec.capped(rc, RnRecovery.Dec.r(RnRecovery.rec.long(u, RnRecovery.Rk.longs(k, row), same, last, RnRecovery.Rec{k, row, same, last}))) == True{} : Bool}:
  match u:
    case True{}:
      below_up(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc), e)
    case False{}:
      ok

# a length stop with no text: a compaction keeps the row, a note under the
# cap and the last rung (the row is the cap) end within cap + 1
def cap_think(+rc: RnRecovery.RCfg, s: Bool, u: Bool, lower: Bool, q: Bool, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, e: {RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)) == u : Bool}, eq: {Nat.is_eq(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)) == q : Bool}, ok: {RnRecovery.Rk.capped(rc, k, row) == True{} : Bool}) -> {RnRecovery.Rec.capped(rc, RnRecovery.Dec.r(RnRecovery.rec.think(s, u, Bool.and(lower, q), RnRecovery.Rk.longs(k, row), same, last, RnRecovery.Rec{k, row, same, last}))) == True{} : Bool}:
  match s:
    case True{}:
      ok
    case False{}:
      match u:
        case True{}:
          below_up(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc), e)
        case False{}:
          match lower:
            case False{}:
              ok
            case True{}:
              match q:
                case True{}:
                  below_eq(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc), eq)
                case False{}:
                  ok

def cap_leak(+rc: RnRecovery.RCfg, u: Bool, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, e: {RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)) == u : Bool}, ok: {RnRecovery.Rk.capped(rc, k, row) == True{} : Bool}) -> {RnRecovery.Rec.capped(rc, RnRecovery.Dec.r(RnRecovery.rec.leak(u, RnRecovery.Rk.leaks(k, row), same, last, RnRecovery.Rec{k, row, same, last}))) == True{} : Bool}:
  match u:
    case True{}:
      e
    case False{}:
      ok

def cap_ran(+rc: RnRecovery.RCfg, fresh: Bool, u: Bool, kept: Bool, +m: Nat, +h: Nat, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, e: {RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)) == u : Bool}, ok: {RnRecovery.Rk.capped(rc, k, row) == True{} : Bool}) -> {RnRecovery.Rec.capped(rc, RnRecovery.Dec.r(RnRecovery.rec.ran(fresh, u, kept, m, h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last}))) == True{} : Bool}:
  match fresh u:
    case True{} u:
      {==}
    case False{} True{}:
      e
    case False{} False{}:
      ok

def cap_empty(+rc: RnRecovery.RCfg, u: Bool, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, e: {RnRecovery.below(RnRecovery.Rk.empties(k, row), Stop.empty_cap()) == u : Bool}, ok: {RnRecovery.Rk.capped(rc, k, row) == True{} : Bool}) -> {RnRecovery.Rec.capped(rc, RnRecovery.Dec.r(RnRecovery.rec.empty(u, RnRecovery.Rk.empties(k, row), same, last, RnRecovery.Rec{k, row, same, last}))) == True{} : Bool}:
  match u:
    case True{}:
      e
    case False{}:
      ok

def cap_out(+rc: RnRecovery.RCfg, o: RnRecovery.Out, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, ok: {RnRecovery.Rk.capped(rc, k, row) == True{} : Bool}) -> {RnRecovery.Rec.capped(rc, RnRecovery.Dec.r(RnRecovery.rec.go(rc, o, k, row, same, last))) == True{} : Bool}:
  match o:
    case RnRecovery.Long{}:
      cap_long(rc, RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)), k, row, same, last, {==}, ok)
    case RnRecovery.Leak{rebuilt, +h, kept}:
      match rebuilt:
        case True{}:
          cap_ran(rc, RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)), RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, k, row, same, last, {==}, ok)
        case False{}:
          cap_leak(rc, RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)), k, row, same, last, {==}, ok)
    case RnRecovery.Ran{+h, kept}:
      cap_ran(rc, RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)), RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, k, row, same, last, {==}, ok)
    case RnRecovery.Noted{}:
      {==}
    case RnRecovery.Said{}:
      ok
    case RnRecovery.Answer{}:
      {==}
    case RnRecovery.Other{}:
      ok
    case RnRecovery.Empty{}:
      cap_empty(rc, RnRecovery.below(RnRecovery.Rk.empties(k, row), Stop.empty_cap()), k, row, same, last, {==}, ok)
    case RnRecovery.Think{shrink, lower}:
      cap_think(rc, shrink, RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)), lower, Nat.is_eq(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)), k, row, same, last, {==}, {==}, ok)

def cap_step(+rc: RnRecovery.RCfg, o: RnRecovery.Out, r: RnRecovery.Rec, ok: {RnRecovery.Rec.capped(rc, r) == True{} : Bool}) -> {RnRecovery.Rec.capped(rc, RnRecovery.Dec.r(RnRecovery.Rec.step(rc, o, r))) == True{} : Bool}:
  match r:
    case RnRecovery.Rec{k, row, same, last}:
      cap_out(rc, o, k, row, same, last, ok)

def cap_go(os: List<&2, RnRecovery.Out>, +rc: RnRecovery.RCfg, +r: RnRecovery.Rec, ok: {RnRecovery.Rec.capped(rc, r) == True{} : Bool}) -> {RnRecovery.Rec.capped(rc, RnRecovery.Rec.go(os, rc, r)) == True{} : Bool}:
  match os:
    case Nil{}:
      ok
    case +o <> rest:
      cap_go(rest, rc, RnRecovery.Dec.r(RnRecovery.Rec.step(rc, o, r)), cap_step(rc, o, r, ok))

def notes_capped(+rc: RnRecovery.RCfg, +os: List<&2, RnRecovery.Out>) -> {RnRecovery.Rec.capped(rc, RnRecovery.Rec.run(rc, os)) == True{} : Bool}:
  cap_go(os, rc, RnRecovery.Rec.init(), {==})

def Run.rec_notes_capped(rc, os):
  notes_capped(rc, os)

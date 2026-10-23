# eukhe: the proof of LAW rec_never_runs_a_repeat

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run.bend as Run
import ../base/bool/misc.bend as LBoolMisc

# ---- recover ----

# proof_recover: the H4.8 recovery laws of LAWS.bend about the
# recoveries (Rec) of bend/run.bend.
#
# - the one-step laws (length, leak, repeat, a user message): by
#   computation, after a rewrite of each cap test with its premise.
# - stuck_gets_help: by computation on each stuck reply and each value
#   of its cap tests: no branch passes the reply on as it is.
# - notes_capped: an invariant of the recoveries, by induction on the
#   replies. A recovery adds a note only under its cap, so the row of
#   the next note is at most the cap of its recovery.
# - never_runs_a_repeat: an invariant, by induction on the replies. Calls
#   run only when the rounds in a row that they make stay below the
#   repeat cap (and a round whose results change starts a new row of 1,
#   which is below the cap too, as the call ran); every other reply keeps
#   the count or clears it.

# Numbers
# -------

def max_zero(n: Nat) -> {Nat.max(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# m < b, so m < max(b, 1)
def below_max(m: Nat, b: Nat, e: {RnRecovery.below(m, b) == True{} : Bool}) -> {RnRecovery.below(m, Nat.max(b, 1n)) == True{} : Bool}:
  match m b:
    case 0n 0n:
      LBoolMisc.absurd({RnRecovery.below(0n, Nat.max(0n, 1n)) == True{} : Bool}, e)
    case 1n+p 0n:
      LBoolMisc.absurd({RnRecovery.below(1n+p, Nat.max(0n, 1n)) == True{} : Bool}, e)
    case m 1n+q:
      %Equal.sym(Nat, Nat.max(q, 0n), q, max_zero(q)) : {RnRecovery.below(m, 1n+_) == True{} : Bool}
      e

def zero_below_max(b: Nat) -> {RnRecovery.below(0n, Nat.max(b, 1n)) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

# x < q, so 0 < q
def one_below_q(x: Nat, q: Nat, e: {RnRecovery.below(x, q) == True{} : Bool}) -> {RnRecovery.below(0n, q) == True{} : Bool}:
  match x q:
    case 0n 0n:
      LBoolMisc.absurd({RnRecovery.below(0n, 0n) == True{} : Bool}, e)
    case 1n+p 0n:
      LBoolMisc.absurd({RnRecovery.below(0n, 0n) == True{} : Bool}, e)
    case x 1n+r:
      {==}

# 0 < m and m < b, so 1 < max(b, 1)
def one_below_max(m: Nat, +b: Nat, pos: {RnRecovery.below(0n, m) == True{} : Bool}, e: {RnRecovery.below(m, b) == True{} : Bool}) -> {RnRecovery.below(1n, Nat.max(b, 1n)) == True{} : Bool}:
  match m b:
    case 0n b:
      LBoolMisc.absurd({RnRecovery.below(1n, Nat.max(b, 1n)) == True{} : Bool}, pos)
    case 1n+x 0n:
      LBoolMisc.absurd({RnRecovery.below(1n, Nat.max(0n, 1n)) == True{} : Bool}, e)
    case 1n+x 1n+q:
      %Equal.sym(Nat, Nat.max(q, 0n), q, max_zero(q)) : {RnRecovery.below(1n, 1n+_) == True{} : Bool}
      one_below_q(x, q, e)

def again_eq_pos(b: Bool, k: Nat) -> {RnRecovery.below(0n, RnRecovery.again.eq(b, k)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a round makes at least one round in a row
def again_pos(same: Nat, +last: Nat, +h: Nat) -> {RnRecovery.below(0n, RnRecovery.again(same, last, h)) == True{} : Bool}:
  match same:
    case 0n:
      {==}
    case 1n+k:
      again_eq_pos(Nat.is_eq(last, h), k)

# No call runs a repeat
# ---------------------

def same_long(u: Bool, -M: Nat, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, ok: {RnRecovery.below(same, M) == True{} : Bool}) -> {RnRecovery.below(RnRecovery.Rec.same(RnRecovery.Dec.r(RnRecovery.rec.long(u, RnRecovery.Rk.longs(k, row), same, last, RnRecovery.Rec{k, row, same, last}))), M) == True{} : Bool}:
  match u:
    case True{}:
      ok
    case False{}:
      ok

def same_leak(u: Bool, -M: Nat, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, ok: {RnRecovery.below(same, M) == True{} : Bool}) -> {RnRecovery.below(RnRecovery.Rec.same(RnRecovery.Dec.r(RnRecovery.rec.leak(u, RnRecovery.Rk.leaks(k, row), same, last, RnRecovery.Rec{k, row, same, last}))), M) == True{} : Bool}:
  match u:
    case True{}:
      ok
    case False{}:
      ok

# a round that ran: m < repeat, so whichever row it makes is below the cap
def same_kept(kept: Bool, +m: Nat, +b: Nat, pos: {RnRecovery.below(0n, m) == True{} : Bool}, e: {RnRecovery.below(m, b) == True{} : Bool}) -> {RnRecovery.below(RnRecovery.ran.same(kept, m), Nat.max(b, 1n)) == True{} : Bool}:
  match kept:
    case True{}:
      below_max(m, b, e)
    case False{}:
      one_below_max(m, b, pos, e)

def same_ran(+rc: RnRecovery.RCfg, fresh: Bool, u: Bool, kept: Bool, +m: Nat, +h: Nat, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, pos: {RnRecovery.below(0n, m) == True{} : Bool}, e: {RnRecovery.below(m, RnRecovery.RCfg.repeat(rc)) == fresh : Bool}, ok: {RnRecovery.below(same, Nat.max(RnRecovery.RCfg.repeat(rc), 1n)) == True{} : Bool}) -> {RnRecovery.below(RnRecovery.Rec.same(RnRecovery.Dec.r(RnRecovery.rec.ran(fresh, u, kept, m, h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last}))), Nat.max(RnRecovery.RCfg.repeat(rc), 1n)) == True{} : Bool}:
  match fresh u:
    case True{} u:
      same_kept(kept, m, RnRecovery.RCfg.repeat(rc), pos, e)
    case False{} True{}:
      ok
    case False{} False{}:
      ok

def same_out(+rc: RnRecovery.RCfg, o: RnRecovery.Out, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, ok: {RnRecovery.below(same, Nat.max(RnRecovery.RCfg.repeat(rc), 1n)) == True{} : Bool}) -> {RnRecovery.below(RnRecovery.Rec.same(RnRecovery.Dec.r(RnRecovery.rec.go(rc, o, k, row, same, last))), Nat.max(RnRecovery.RCfg.repeat(rc), 1n)) == True{} : Bool}:
  match o:
    case RnRecovery.Long{}:
      same_long(RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)), Nat.max(RnRecovery.RCfg.repeat(rc), 1n), k, row, same, last, ok)
    case RnRecovery.Leak{rebuilt, +h, kept}:
      match rebuilt:
        case True{}:
          same_ran(rc, RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)), RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, k, row, same, last, again_pos(same, last, h), {==}, ok)
        case False{}:
          same_leak(RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)), Nat.max(RnRecovery.RCfg.repeat(rc), 1n), k, row, same, last, ok)
    case RnRecovery.Ran{+h, kept}:
      same_ran(rc, RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)), RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, k, row, same, last, again_pos(same, last, h), {==}, ok)
    case RnRecovery.Noted{}:
      ok
    case RnRecovery.Said{}:
      zero_below_max(RnRecovery.RCfg.repeat(rc))
    case RnRecovery.Answer{}:
      zero_below_max(RnRecovery.RCfg.repeat(rc))
    case RnRecovery.Other{}:
      ok

def same_step(+rc: RnRecovery.RCfg, o: RnRecovery.Out, r: RnRecovery.Rec, ok: {RnRecovery.below(RnRecovery.Rec.same(r), Nat.max(RnRecovery.RCfg.repeat(rc), 1n)) == True{} : Bool}) -> {RnRecovery.below(RnRecovery.Rec.same(RnRecovery.Dec.r(RnRecovery.Rec.step(rc, o, r))), Nat.max(RnRecovery.RCfg.repeat(rc), 1n)) == True{} : Bool}:
  match r:
    case RnRecovery.Rec{k, row, same, last}:
      same_out(rc, o, k, row, same, last, ok)

def same_go(os: List<&2, RnRecovery.Out>, +rc: RnRecovery.RCfg, +r: RnRecovery.Rec, ok: {RnRecovery.below(RnRecovery.Rec.same(r), Nat.max(RnRecovery.RCfg.repeat(rc), 1n)) == True{} : Bool}) -> {RnRecovery.below(RnRecovery.Rec.same(RnRecovery.Rec.go(os, rc, r)), Nat.max(RnRecovery.RCfg.repeat(rc), 1n)) == True{} : Bool}:
  match os:
    case Nil{}:
      ok
    case +o <> rest:
      same_go(rest, rc, RnRecovery.Dec.r(RnRecovery.Rec.step(rc, o, r)), same_step(rc, o, r, ok))

def never_runs_a_repeat(+rc: RnRecovery.RCfg, +os: List<&2, RnRecovery.Out>) -> {RnRecovery.below(RnRecovery.Rec.same(RnRecovery.Rec.run(rc, os)), Nat.max(RnRecovery.RCfg.repeat(rc), 1n)) == True{} : Bool}:
  same_go(os, rc, RnRecovery.Rec.init(), zero_below_max(RnRecovery.RCfg.repeat(rc)))

def Run.rec_never_runs_a_repeat(rc, os):
  never_runs_a_repeat(rc, os)

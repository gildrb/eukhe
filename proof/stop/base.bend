# eukhe: lemmas shared by the proofs of area stop: the walk is the
# spec's case by case (stb.walk), the model's window test is the spec's
# (stb.bound, stb.full), a spelled request reads back (stb.req), the
# answer is the spelled spec answer (stb.reply), and `recover` on an
# empty reply and on a length stop is the spec's (stb.empty_recover,
# stb.think_recover).

import Base
import ../../bend/stop.bend as S
import ../../bend/ffi_stop.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/stop.bend as Stop
import ../../spec/harness/stop.bend as StSpec
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision

# Logic
# -----

def stb.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def stb.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : stb.BD(_, A, Unit)
  Unit{}

def stb.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def stb.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      stb.absurd({b == True{} : Bool}, h)

# The verdicts and the walk
# -------------------------

def stb.on(b: Bool) -> {S.on(b) == StSpec.go_if(b) : S.Verdict}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def stb.verdict(d: S.Dir, f: S.Facts) -> {S.verdict(d, f) == StSpec.verdict(d, f) : S.Verdict}:
  match d:
    case S.LengthStop{}:
      match f:
        case S.Facts{c, t, b, p, sp, cu}:
          match c:
            case True{}:
              match t:
                case True{}:
                  match sp:
                    case True{}:
                      match cu:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      {==}
                case False{}:
                  {==}
            case False{}:
              {==}
    case S.EmptyStop{}:
      match f:
        case S.Facts{c, t, b, p, sp, cu}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case S.MarkupStop{}:
      match f:
        case S.Facts{c, t, b, p, sp, cu}:
          stb.on(b)
    case S.PendingWork{}:
      match f:
        case S.Facts{c, t, b, p, sp, cu}:
          match p:
            case True{}:
              {==}
            case False{}:
              {==}

def stb.walk(f: S.Facts) -> {S.walk(f) == StSpec.pick(f) : S.Pick}:
  match f:
    case S.Facts{c, t, b, p, sp, cu}:
      match c:
        case True{}:
          match t:
            case False{}:
              {==}
            case True{}:
              match sp:
                case True{}:
                  match cu:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  {==}
        case False{}:
          match t:
            case False{}:
              {==}
            case True{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  match p:
                    case True{}:
                      {==}
                    case False{}:
                      {==}

# The window
# ----------

# the spec's window test is the model's
def stb.bound(+w: Nat, +c: Nat, +p: Nat, +o: Nat) -> {StSpec.ran_out(w, c, p, o) == RnRecovery.bound(w, c, p, o) : Bool}:
  match w:
    case 0n:
      {==}
    case 1n+v:
      {==}

# the spec's full is the model's: the same window test, the same
# compaction
def stb.full(+w: Nat, +c: Nat, +p: Nat, +o: Nat, cu: Bool) -> {StSpec.full(w, c, p, o, cu) == RnRecovery.full(w, c, p, o, cu) : Bool}:
  %stb.bound(w, c, p, o) : {Bool.and(cu, StSpec.ran_out(w, c, p, o)) == Bool.and(cu, _) : Bool}
  {==}

# The entry
# ---------

# a spelled request that fits reads back, the rest untouched
def stb.req(q: FS.Ask, +rest: String, +h: {Stop.sp_fit(q) == True{} : Bool}) -> {FS.get_ask(Stop.sp_w_ask(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FS.Ask>}:
  match q:
    case FS.AskWalk{+c, +t, +b, +p, +w, +ca, +pr, +o, +cu}:
      +fw = LawsBase.wire_fits(w)
      +fc = LawsBase.wire_fits(ca)
      +fp = LawsBase.wire_fits(pr)
      +fo = LawsBase.wire_fits(o)
      +ha = stb.and_l(Bool.and(fw, fc), Bool.and(fp, fo), h)
      +hb = stb.and_r(Bool.and(fw, fc), Bool.and(fp, fo), h)
      +r8 = Wr.put_bool(cu, rest)
      +r7 = Wr.put_nat(o, r8)
      +r6 = Wr.put_nat(pr, r7)
      +r5 = Wr.put_nat(ca, r6)
      +r4 = Wr.put_nat(w, r5)
      +r3 = Wr.put_bool(p, r4)
      +r2 = Wr.put_bool(b, r3)
      +r1 = Wr.put_bool(t, r2)
      +x = {FS.AskWalk{c, t, b, p, w, ca, pr, o, cu} : FS.Ask}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(c, r1)), Wr.Got{c, r1}, Wire.wire_bool_round_trip(c, r1)) : {FS.get_walk(_) == Wr.Got{x, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r1), Wr.Got{t, r2}, Wire.wire_bool_round_trip(t, r2)) : {FS.get_walk.text(c, _) == Wr.Got{x, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r2), Wr.Got{b, r3}, Wire.wire_bool_round_trip(b, r3)) : {FS.get_walk.broken(c, t, _) == Wr.Got{x, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r3), Wr.Got{p, r4}, Wire.wire_bool_round_trip(p, r4)) : {FS.get_walk.pending(c, t, b, _) == Wr.Got{x, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r4), Wr.Got{w, r5}, Wire.wire_nat_round_trip(w, r5, stb.and_l(fw, fc, ha))) : {FS.get_walk.window(c, t, b, p, _) == Wr.Got{x, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r5), Wr.Got{ca, r6}, Wire.wire_nat_round_trip(ca, r6, stb.and_r(fw, fc, ha))) : {FS.get_walk.catalog(c, t, b, p, w, _) == Wr.Got{x, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r6), Wr.Got{pr, r7}, Wire.wire_nat_round_trip(pr, r7, stb.and_l(fp, fo, hb))) : {FS.get_walk.prompt(c, t, b, p, w, ca, _) == Wr.Got{x, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r7), Wr.Got{o, r8}, Wire.wire_nat_round_trip(o, r8, stb.and_r(fp, fo, hb))) : {FS.get_walk.out(c, t, b, p, w, ca, pr, _) == Wr.Got{x, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r8), Wr.Got{cu, rest}, Wire.wire_bool_round_trip(cu, rest)) : {FS.get_walk.cuttable(c, t, b, p, w, ca, pr, o, _) == Wr.Got{x, rest} : Wr.Dec<FS.Ask>}
      {==}
    case FS.AskRounds{+m, +d}:
      +h0 = stb.and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(d), h)
      +h1 = stb.and_r(LawsBase.wire_fits(m), LawsBase.wire_fits(d), h)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(m, Wr.put_nat(d, rest))), Wr.Got{m, Wr.put_nat(d, rest)}, Wire.wire_nat_round_trip(m, Wr.put_nat(d, rest), h0)) : {FS.get_rounds(_) == Wr.Got{FS.AskRounds{m, d}, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(d, rest)), Wr.Got{d, rest}, Wire.wire_nat_round_trip(d, rest, h1)) : {FS.get_rounds.done(m, _) == Wr.Got{FS.AskRounds{m, d}, rest} : Wr.Dec<FS.Ask>}
      {==}

# the spelled pick of the code's walk is the spelled pick of the spec's
def stb.w_pick(p: S.Pick) -> {FS.put_pick(p, "") == Stop.sp_w_pick(p) : String}:
  match p:
    case S.Stands{}:
      {==}
    case S.Goes{d}:
      match d:
        case S.LengthStop{}:
          {==}
        case S.EmptyStop{}:
          {==}
        case S.MarkupStop{}:
          {==}
        case S.PendingWork{}:
          {==}
    case S.Drops{}:
      {==}

def stb.w_round(m: Maybe<&2, String>) -> {FS.put_text(m, "") == Stop.sp_w_round(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      {==}

# The round note
# --------------

def stb.round_text(left: Nat, +max: Nat) -> {S.rounds.text(left, max) == StSpec.round_text(left, max) : String}:
  match left:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def stb.round_at(near: Bool, +left: Nat, +max: Nat) -> {S.rounds.at(near, left, max) == StSpec.round_at(near, left, max) : Maybe<&2, String>}:
  match near:
    case True{}:
      Equal.cong(String, Maybe<&2, String>, z => Some{z}, S.rounds.text(left, max), StSpec.round_text(left, max), stb.round_text(left, max))
    case False{}:
      {==}

# the round note after any rounds of any cap is the spec's
def stb.rounds(+m: Nat, +d: Nat) -> {S.rounds(m, d) == StSpec.rounds(m, d) : Maybe<&2, String>}:
  +l = Nat.sub(Nat.sub(m, 1n), d)
  stb.round_at(Nat.is_le(l, 10n), l, m)

# the entry's answer to a request is the spelled spec answer: the stop
# the entry reads from the window is the spec's (stb.bound)
def stb.reply(q: FS.Ask) -> {FS.answer(q) == Stop.sp_w_reply(q) : String}:
  match q:
    case FS.AskWalk{+c, +t, +b, +p, +w, +ca, +pr, +o, +cu}:
      +f = {S.Facts{c, t, b, p, StSpec.ran_out(w, ca, pr, o), cu} : S.Facts}
      %stb.bound(w, ca, pr, o) : {FS.put_pick(S.walk(S.Facts{c, t, b, p, _, cu}), "") == Stop.sp_w_pick(StSpec.pick(f)) : String}
      %Equal.sym(S.Pick, S.walk(f), StSpec.pick(f), stb.walk(f)) : {FS.put_pick(_, "") == Stop.sp_w_pick(StSpec.pick(f)) : String}
      stb.w_pick(StSpec.pick(f))
    case FS.AskRounds{+m, +d}:
      %Equal.sym(Maybe<&2, String>, S.rounds(m, d), StSpec.rounds(m, d), stb.rounds(m, d)) : {FS.put_text(_, "") == Stop.sp_w_reply(FS.AskRounds{m, d}) : String}
      stb.w_round(StSpec.rounds(m, d))

# The ladder
# ----------

# the model's test of a row under the cap is Nat's
def stb.below(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == RnRecovery.below(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      stb.below(p, q)

# a row at the cap is not under it
def stb.eq_not_below(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {RnRecovery.below(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      stb.absurd({RnRecovery.below(0n, 1n+q) == False{} : Bool}, h)
    case 1n+p 0n:
      stb.absurd({RnRecovery.below(1n+p, 0n) == False{} : Bool}, h)
    case 1n+p 1n+q:
      stb.eq_not_below(p, q, h)

# a row one past the cap is neither under it nor at it
def stb.succ_not_below(+m: Nat) -> {RnRecovery.below(1n+m, m) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      stb.succ_not_below(q)

def stb.succ_not_eq(+m: Nat) -> {Nat.is_eq(1n+m, m) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      stb.succ_not_eq(q)

# a rung that remains never fails the run
def stb.think_left(s: Bool, u: Bool, l: Bool, -x: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec, h: {Bool.or(s, Bool.or(u, l)) == True{} : Bool}) -> {Stop.quits(RnRecovery.Dec.act(RnRecovery.rec.think(s, u, l, x, same, last, r))) == False{} : Bool}:
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
              stb.absurd({Stop.quits(RnRecovery.Dec.act(RnRecovery.rec.think(False{}, False{}, False{}, x, same, last, r))) == False{} : Bool}, h)

# with every rung spent the run fails, the row as it was
def stb.think_spent(s: Bool, u: Bool, l: Bool, -x: Nat, -same: Nat, -last: Nat, +r: RnRecovery.Rec, h: {Bool.or(s, Bool.or(u, l)) == False{} : Bool}) -> {RnRecovery.rec.think(s, u, l, x, same, last, r) == RnRecovery.Dec{RnRecovery.Quit{}, r} : RnRecovery.Dec}:
  match s:
    case True{}:
      stb.absurd({RnRecovery.rec.think(True{}, u, l, x, same, last, r) == RnRecovery.Dec{RnRecovery.Quit{}, r} : RnRecovery.Dec}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      match u:
        case True{}:
          stb.absurd({RnRecovery.rec.think(False{}, True{}, l, x, same, last, r) == RnRecovery.Dec{RnRecovery.Quit{}, r} : RnRecovery.Dec}, Equal.sym(Bool, True{}, False{}, h))
        case False{}:
          match l:
            case True{}:
              stb.absurd({RnRecovery.rec.think(False{}, False{}, True{}, x, same, last, r) == RnRecovery.Dec{RnRecovery.Quit{}, r} : RnRecovery.Dec}, Equal.sym(Bool, True{}, False{}, h))
            case False{}:
              {==}

# The rows and `recover`
# ----------------------

# the code's count of empty notes is decide.rs `NoteCause::row`
def stb.empty_row(+k: RnRecovery.Rk, +row: Nat) -> {RnRecovery.Rk.empties(k, row) == Stop.rust_empty_row(k, row) : Nat}:
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

# the code's count of length notes is decide.rs `NoteCause::row`
def stb.long_row(+k: RnRecovery.Rk, +row: Nat) -> {RnRecovery.Rk.longs(k, row) == Stop.rust_long_row(k, row) : Nat}:
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

def stb.empty(+b: Bool, +n: Nat, +same: Nat, +last: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.empty(b, n, same, last, r)) == Stop.rust_empty.at(b, n) : RnDecision.Help}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# `recover` on an empty reply is the spec's
def stb.empty_recover(+rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat) -> {RnDecision.decide.recover(rc, RnDecision.Emptied{}, k, row) == Stop.rust_empty(k, row) : RnDecision.Help}:
  +x = RnRecovery.Rk.empties(k, row)
  +r = {RnRecovery.Rec{k, row, 0n, 0n} : RnRecovery.Rec}
  %stb.empty_row(k, row) : {RnDecision.Help.of(RnRecovery.rec.empty(RnRecovery.below(x, S.empty_cap()), x, 0n, 0n, r)) == Stop.rust_empty.at(Nat.is_lt(_, S.empty_cap()), _) : RnDecision.Help}
  %stb.below(x, S.empty_cap()) : {RnDecision.Help.of(RnRecovery.rec.empty(_, x, 0n, 0n, r)) == Stop.rust_empty.at(Nat.is_lt(x, S.empty_cap()), x) : RnDecision.Help}
  stb.empty(Nat.is_lt(x, S.empty_cap()), x, 0n, 0n, r)

def stb.at_cap(le: Bool, +x: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.think.note(False{}, le, x, 0n, 0n, r)) == StSpec.at_cap(le, x) : RnDecision.Help}:
  match le:
    case True{}:
      {==}
    case False{}:
      {==}

def stb.think_note(lt: Bool, +lower: Bool, +x: Nat, +long: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.think.note(lt, Bool.and(lower, Nat.is_eq(x, long)), x, 0n, 0n, r)) == StSpec.under(lt, lower, x, long) : RnDecision.Help}:
  match lt:
    case True{}:
      {==}
    case False{}:
      stb.at_cap(Bool.and(lower, Nat.is_eq(x, long)), x, r)

def stb.think(s: Bool, +lower: Bool, +x: Nat, +long: Nat, +r: RnRecovery.Rec) -> {RnDecision.Help.of(RnRecovery.rec.think(s, Nat.is_lt(x, long), Bool.and(lower, Nat.is_eq(x, long)), x, 0n, 0n, r)) == StSpec.ladder(s, lower, x, long) : RnDecision.Help}:
  match s:
    case True{}:
      {==}
    case False{}:
      stb.think_note(Nat.is_lt(x, long), lower, x, long, r)

# `recover` on a length stop is the spec's ladder
def stb.think_recover(+long: Nat, +leak: Nat, +redirect: Nat, +repeat: Nat, +k: RnRecovery.Rk, +row: Nat, +w: Nat, +c: Nat, +p: Nat, +o: Nat, +cu: Bool, +lo: Bool) -> {RnDecision.decide.recover(RnRecovery.RCfg{long, leak, redirect, repeat}, RnDecision.Thought{w, c, p, o, cu, lo}, k, row) == Stop.rust_think(long, k, row, w, c, p, o, cu, lo) : RnDecision.Help}:
  +x = RnRecovery.Rk.longs(k, row)
  +r = {RnRecovery.Rec{k, row, 0n, 0n} : RnRecovery.Rec}
  %stb.long_row(k, row) : {RnDecision.Help.of(RnRecovery.rec.think(Bool.and(cu, RnRecovery.bound(w, c, p, o)), RnRecovery.below(x, long), Bool.and(lo, Nat.is_eq(x, long)), x, 0n, 0n, r)) == StSpec.ladder(Bool.and(cu, StSpec.ran_out(w, c, p, o)), lo, _, long) : RnDecision.Help}
  %stb.bound(w, c, p, o) : {RnDecision.Help.of(RnRecovery.rec.think(Bool.and(cu, _), RnRecovery.below(x, long), Bool.and(lo, Nat.is_eq(x, long)), x, 0n, 0n, r)) == StSpec.ladder(Bool.and(cu, StSpec.ran_out(w, c, p, o)), lo, x, long) : RnDecision.Help}
  %stb.below(x, long) : {RnDecision.Help.of(RnRecovery.rec.think(Bool.and(cu, StSpec.ran_out(w, c, p, o)), _, Bool.and(lo, Nat.is_eq(x, long)), x, 0n, 0n, r)) == StSpec.ladder(Bool.and(cu, StSpec.ran_out(w, c, p, o)), lo, x, long) : RnDecision.Help}
  stb.think(Bool.and(cu, StSpec.ran_out(w, c, p, o)), lo, x, long, r)

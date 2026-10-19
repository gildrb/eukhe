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

import Base
import ./run.bend as R
import ./proof_run.bend as Runs

# Numbers
# -------

def max_zero(n: Nat) -> {Nat.max(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# m < b, so m < max(b, 1)
def below_max(m: Nat, b: Nat, e: {R.below(m, b) == True{} : Bool}) -> {R.below(m, Nat.max(b, 1n)) == True{} : Bool}:
  match m b:
    case 0n 0n:
      Runs.absurd({R.below(0n, Nat.max(0n, 1n)) == True{} : Bool}, e)
    case 1n+p 0n:
      Runs.absurd({R.below(1n+p, Nat.max(0n, 1n)) == True{} : Bool}, e)
    case m 1n+q:
      %Equal.sym(Nat, Nat.max(q, 0n), q, max_zero(q)) : {R.below(m, 1n+_) == True{} : Bool}
      e

def zero_below_max(b: Nat) -> {R.below(0n, Nat.max(b, 1n)) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

# x < q, so 0 < q
def one_below_q(x: Nat, q: Nat, e: {R.below(x, q) == True{} : Bool}) -> {R.below(0n, q) == True{} : Bool}:
  match x q:
    case 0n 0n:
      Runs.absurd({R.below(0n, 0n) == True{} : Bool}, e)
    case 1n+p 0n:
      Runs.absurd({R.below(0n, 0n) == True{} : Bool}, e)
    case x 1n+r:
      {==}

# 0 < m and m < b, so 1 < max(b, 1)
def one_below_max(m: Nat, +b: Nat, pos: {R.below(0n, m) == True{} : Bool}, e: {R.below(m, b) == True{} : Bool}) -> {R.below(1n, Nat.max(b, 1n)) == True{} : Bool}:
  match m b:
    case 0n b:
      Runs.absurd({R.below(1n, Nat.max(b, 1n)) == True{} : Bool}, pos)
    case 1n+x 0n:
      Runs.absurd({R.below(1n, Nat.max(0n, 1n)) == True{} : Bool}, e)
    case 1n+x 1n+q:
      %Equal.sym(Nat, Nat.max(q, 0n), q, max_zero(q)) : {R.below(1n, 1n+_) == True{} : Bool}
      one_below_q(x, q, e)

def again_eq_pos(b: Bool, k: Nat) -> {R.below(0n, R.again.eq(b, k)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a round makes at least one round in a row
def again_pos(same: Nat, +last: Nat, +h: Nat) -> {R.below(0n, R.again(same, last, h)) == True{} : Bool}:
  match same:
    case 0n:
      {==}
    case 1n+k:
      again_eq_pos(Nat.is_eq(last, h), k)

# The one-step laws
# -----------------

def length_retries_with_a_note(+rc: R.RCfg, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, under: {R.below(R.Rk.longs(k, row), R.RCfg.long(rc)) == True{} : Bool}) -> {R.Rec.step(rc, R.Long{}, R.Rec{k, row, same, last}) == R.Dec{R.Redo{}, R.Rec{R.Longs{}, 1n+R.Rk.longs(k, row), same, last}} : R.Dec}:
  %Equal.sym(Bool, R.below(R.Rk.longs(k, row), R.RCfg.long(rc)), True{}, under) : {R.rec.long(_, R.Rk.longs(k, row), same, last, R.Rec{k, row, same, last}) == R.Dec{R.Redo{}, R.Rec{R.Longs{}, 1n+R.Rk.longs(k, row), same, last}} : R.Dec}
  {==}

def length_gives_up(+rc: R.RCfg, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, over: {R.below(R.Rk.longs(k, row), R.RCfg.long(rc)) == False{} : Bool}) -> {R.Dec.act(R.Rec.step(rc, R.Long{}, R.Rec{k, row, same, last})) == R.Quit{} : R.Act}:
  %Equal.sym(Bool, R.below(R.Rk.longs(k, row), R.RCfg.long(rc)), False{}, over) : {R.Dec.act(R.rec.long(_, R.Rk.longs(k, row), same, last, R.Rec{k, row, same, last})) == R.Quit{} : R.Act}
  {==}

def leak_rebuilt_is_calls(+rc: R.RCfg, +h: Nat, kept: Bool, r: R.Rec) -> {R.Rec.step(rc, R.Leak{True{}, h, kept}, r) == R.Rec.step(rc, R.Ran{h, kept}, r) : R.Dec}:
  match r:
    case R.Rec{k, row, same, last}:
      {==}

def leak_retries_with_a_note(+rc: R.RCfg, +h: Nat, kept: Bool, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, under: {R.below(R.Rk.leaks(k, row), R.RCfg.leak(rc)) == True{} : Bool}) -> {R.Rec.step(rc, R.Leak{False{}, h, kept}, R.Rec{k, row, same, last}) == R.Dec{R.Redo{}, R.Rec{R.Leaks{}, 1n+R.Rk.leaks(k, row), same, last}} : R.Dec}:
  %Equal.sym(Bool, R.below(R.Rk.leaks(k, row), R.RCfg.leak(rc)), True{}, under) : {R.rec.leak(_, R.Rk.leaks(k, row), same, last, R.Rec{k, row, same, last}) == R.Dec{R.Redo{}, R.Rec{R.Leaks{}, 1n+R.Rk.leaks(k, row), same, last}} : R.Dec}
  {==}

def leak_stands(+rc: R.RCfg, +h: Nat, kept: Bool, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, over: {R.below(R.Rk.leaks(k, row), R.RCfg.leak(rc)) == False{} : Bool}) -> {R.Dec.act(R.Rec.step(rc, R.Leak{False{}, h, kept}, R.Rec{k, row, same, last})) == R.Stand{} : R.Act}:
  %Equal.sym(Bool, R.below(R.Rk.leaks(k, row), R.RCfg.leak(rc)), False{}, over) : {R.Dec.act(R.rec.leak(_, R.Rk.leaks(k, row), same, last, R.Rec{k, row, same, last})) == R.Stand{} : R.Act}
  {==}

def calls_run(+rc: R.RCfg, +h: Nat, +kept: Bool, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, fresh: {R.below(R.again(same, last, h), R.RCfg.repeat(rc)) == True{} : Bool}) -> {R.Rec.step(rc, R.Ran{h, kept}, R.Rec{k, row, same, last}) == R.Dec{R.Exec{}, R.Rec{R.Free{}, 0n, R.ran.same(kept, R.again(same, last, h)), h}} : R.Dec}:
  %Equal.sym(Bool, R.below(R.again(same, last, h), R.RCfg.repeat(rc)), True{}, fresh) : {R.rec.ran(_, R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), kept, R.again(same, last, h), h, R.Rk.loops(k, row), same, last, R.Rec{k, row, same, last}) == R.Dec{R.Exec{}, R.Rec{R.Free{}, 0n, R.ran.same(kept, R.again(same, last, h)), h}} : R.Dec}
  {==}

# a repeat never runs, under the redirect cap or at it
def repeat_runs_not(u: Bool, -kept: Bool, -m: Nat, -h: Nat, -n: Nat, -same: Nat, -last: Nat, -r: R.Rec) -> {R.Act.runs(R.Dec.act(R.rec.ran(False{}, u, kept, m, h, n, same, last, r))) == False{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def repeat_never_runs(+rc: R.RCfg, +h: Nat, kept: Bool, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, rep: {R.below(R.again(same, last, h), R.RCfg.repeat(rc)) == False{} : Bool}) -> {R.Act.runs(R.Dec.act(R.Rec.step(rc, R.Ran{h, kept}, R.Rec{k, row, same, last}))) == False{} : Bool}:
  %Equal.sym(Bool, R.below(R.again(same, last, h), R.RCfg.repeat(rc)), False{}, rep) : {R.Act.runs(R.Dec.act(R.rec.ran(_, R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), kept, R.again(same, last, h), h, R.Rk.loops(k, row), same, last, R.Rec{k, row, same, last}))) == False{} : Bool}
  repeat_runs_not(R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), kept, R.again(same, last, h), h, R.Rk.loops(k, row), same, last, R.Rec{k, row, same, last})

def repeat_redirects(+rc: R.RCfg, +h: Nat, kept: Bool, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, rep: {R.below(R.again(same, last, h), R.RCfg.repeat(rc)) == False{} : Bool}, under: {R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)) == True{} : Bool}) -> {R.Rec.step(rc, R.Ran{h, kept}, R.Rec{k, row, same, last}) == R.Dec{R.Redo{}, R.Rec{R.Loops{}, 1n+R.Rk.loops(k, row), same, last}} : R.Dec}:
  %Equal.sym(Bool, R.below(R.again(same, last, h), R.RCfg.repeat(rc)), False{}, rep) : {R.rec.ran(_, R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), kept, R.again(same, last, h), h, R.Rk.loops(k, row), same, last, R.Rec{k, row, same, last}) == R.Dec{R.Redo{}, R.Rec{R.Loops{}, 1n+R.Rk.loops(k, row), same, last}} : R.Dec}
  %Equal.sym(Bool, R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), True{}, under) : {R.rec.ran(False{}, _, kept, R.again(same, last, h), h, R.Rk.loops(k, row), same, last, R.Rec{k, row, same, last}) == R.Dec{R.Redo{}, R.Rec{R.Loops{}, 1n+R.Rk.loops(k, row), same, last}} : R.Dec}
  {==}

def repeat_gives_up(+rc: R.RCfg, +h: Nat, kept: Bool, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, rep: {R.below(R.again(same, last, h), R.RCfg.repeat(rc)) == False{} : Bool}, over: {R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)) == False{} : Bool}) -> {R.Dec.act(R.Rec.step(rc, R.Ran{h, kept}, R.Rec{k, row, same, last})) == R.Quit{} : R.Act}:
  %Equal.sym(Bool, R.below(R.again(same, last, h), R.RCfg.repeat(rc)), False{}, rep) : {R.Dec.act(R.rec.ran(_, R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), kept, R.again(same, last, h), h, R.Rk.loops(k, row), same, last, R.Rec{k, row, same, last})) == R.Quit{} : R.Act}
  %Equal.sym(Bool, R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), False{}, over) : {R.Dec.act(R.rec.ran(False{}, _, kept, R.again(same, last, h), h, R.Rk.loops(k, row), same, last, R.Rec{k, row, same, last})) == R.Quit{} : R.Act}
  {==}

def user_breaks_the_row(+rc: R.RCfg, +k: R.Rk, +row: Nat, same: Nat, +last: Nat) -> {R.Dec.r(R.Rec.step(rc, R.Said{}, R.Rec{k, row, same, last})) == R.Rec{k, row, 0n, last} : R.Rec}:
  {==}

def redo_is_noted(-pass: R.Reply) -> {R.Act.reply(R.Redo{}, pass) == R.Error{False{}, True{}} : R.Reply}:
  {==}

def quit_fails(+cfg: R.Cfg, -pass: R.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {R.call(cfg, R.Act.reply(R.Quit{}, pass), r, c, a, n, p) == R.St{R.Failed{R.Model{}}, r, c, a, n, p} : R.St}:
  {==}

# A stuck reply always gets help
# ------------------------------

def help_long(u: Bool, -n: Nat, -same: Nat, -last: Nat, -r: R.Rec) -> {R.Act.helps(R.Dec.act(R.rec.long(u, n, same, last, r))) == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def help_leak(u: Bool, -n: Nat, -same: Nat, -last: Nat, -r: R.Rec) -> {R.Act.helps(R.Dec.act(R.rec.leak(u, n, same, last, r))) == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def help_ran(fresh: Bool, u: Bool, -kept: Bool, -m: Nat, -h: Nat, -n: Nat, -same: Nat, -last: Nat, -r: R.Rec) -> {R.Act.helps(R.Dec.act(R.rec.ran(fresh, u, kept, m, h, n, same, last, r))) == True{} : Bool}:
  match fresh u:
    case True{} u:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def help_out(+rc: R.RCfg, o: R.Out, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat) -> {Bool.or(Bool.not(R.Out.stuck(o)), R.Act.helps(R.Dec.act(R.rec.go(rc, o, k, row, same, last)))) == True{} : Bool}:
  match o:
    case R.Long{}:
      help_long(R.below(R.Rk.longs(k, row), R.RCfg.long(rc)), R.Rk.longs(k, row), same, last, R.Rec{k, row, same, last})
    case R.Leak{rebuilt, +h, kept}:
      match rebuilt:
        case True{}:
          help_ran(R.below(R.again(same, last, h), R.RCfg.repeat(rc)), R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), kept, R.again(same, last, h), h, R.Rk.loops(k, row), same, last, R.Rec{k, row, same, last})
        case False{}:
          help_leak(R.below(R.Rk.leaks(k, row), R.RCfg.leak(rc)), R.Rk.leaks(k, row), same, last, R.Rec{k, row, same, last})
    case R.Ran{+h, kept}:
      help_ran(R.below(R.again(same, last, h), R.RCfg.repeat(rc)), R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), kept, R.again(same, last, h), h, R.Rk.loops(k, row), same, last, R.Rec{k, row, same, last})
    case R.Noted{}:
      {==}
    case R.Said{}:
      {==}
    case R.Answer{}:
      {==}
    case R.Other{}:
      {==}

def stuck_gets_help(+rc: R.RCfg, o: R.Out, r: R.Rec) -> {Bool.or(Bool.not(R.Out.stuck(o)), R.Act.helps(R.Dec.act(R.Rec.step(rc, o, r)))) == True{} : Bool}:
  match r:
    case R.Rec{k, row, same, last}:
      help_out(rc, o, k, row, same, last)

# Every recovery stops at its cap
# -------------------------------
# Each lemma takes a cap test u with its equation e, as a match needs a
# parameter.

def cap_long(+rc: R.RCfg, u: Bool, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, e: {R.below(R.Rk.longs(k, row), R.RCfg.long(rc)) == u : Bool}, ok: {R.Rk.capped(rc, k, row) == True{} : Bool}) -> {R.Rec.capped(rc, R.Dec.r(R.rec.long(u, R.Rk.longs(k, row), same, last, R.Rec{k, row, same, last}))) == True{} : Bool}:
  match u:
    case True{}:
      e
    case False{}:
      ok

def cap_leak(+rc: R.RCfg, u: Bool, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, e: {R.below(R.Rk.leaks(k, row), R.RCfg.leak(rc)) == u : Bool}, ok: {R.Rk.capped(rc, k, row) == True{} : Bool}) -> {R.Rec.capped(rc, R.Dec.r(R.rec.leak(u, R.Rk.leaks(k, row), same, last, R.Rec{k, row, same, last}))) == True{} : Bool}:
  match u:
    case True{}:
      e
    case False{}:
      ok

def cap_ran(+rc: R.RCfg, fresh: Bool, u: Bool, kept: Bool, +m: Nat, +h: Nat, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, e: {R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)) == u : Bool}, ok: {R.Rk.capped(rc, k, row) == True{} : Bool}) -> {R.Rec.capped(rc, R.Dec.r(R.rec.ran(fresh, u, kept, m, h, R.Rk.loops(k, row), same, last, R.Rec{k, row, same, last}))) == True{} : Bool}:
  match fresh u:
    case True{} u:
      {==}
    case False{} True{}:
      e
    case False{} False{}:
      ok

def cap_out(+rc: R.RCfg, o: R.Out, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, ok: {R.Rk.capped(rc, k, row) == True{} : Bool}) -> {R.Rec.capped(rc, R.Dec.r(R.rec.go(rc, o, k, row, same, last))) == True{} : Bool}:
  match o:
    case R.Long{}:
      cap_long(rc, R.below(R.Rk.longs(k, row), R.RCfg.long(rc)), k, row, same, last, {==}, ok)
    case R.Leak{rebuilt, +h, kept}:
      match rebuilt:
        case True{}:
          cap_ran(rc, R.below(R.again(same, last, h), R.RCfg.repeat(rc)), R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), kept, R.again(same, last, h), h, k, row, same, last, {==}, ok)
        case False{}:
          cap_leak(rc, R.below(R.Rk.leaks(k, row), R.RCfg.leak(rc)), k, row, same, last, {==}, ok)
    case R.Ran{+h, kept}:
      cap_ran(rc, R.below(R.again(same, last, h), R.RCfg.repeat(rc)), R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), kept, R.again(same, last, h), h, k, row, same, last, {==}, ok)
    case R.Noted{}:
      {==}
    case R.Said{}:
      ok
    case R.Answer{}:
      {==}
    case R.Other{}:
      ok

def cap_step(+rc: R.RCfg, o: R.Out, r: R.Rec, ok: {R.Rec.capped(rc, r) == True{} : Bool}) -> {R.Rec.capped(rc, R.Dec.r(R.Rec.step(rc, o, r))) == True{} : Bool}:
  match r:
    case R.Rec{k, row, same, last}:
      cap_out(rc, o, k, row, same, last, ok)

def cap_go(os: List<&2, R.Out>, +rc: R.RCfg, +r: R.Rec, ok: {R.Rec.capped(rc, r) == True{} : Bool}) -> {R.Rec.capped(rc, R.Rec.go(os, rc, r)) == True{} : Bool}:
  match os:
    case Nil{}:
      ok
    case +o <> rest:
      cap_go(rest, rc, R.Dec.r(R.Rec.step(rc, o, r)), cap_step(rc, o, r, ok))

def notes_capped(+rc: R.RCfg, +os: List<&2, R.Out>) -> {R.Rec.capped(rc, R.Rec.run(rc, os)) == True{} : Bool}:
  cap_go(os, rc, R.Rec.init(), {==})

# No call runs a repeat
# ---------------------

def same_long(u: Bool, -M: Nat, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, ok: {R.below(same, M) == True{} : Bool}) -> {R.below(R.Rec.same(R.Dec.r(R.rec.long(u, R.Rk.longs(k, row), same, last, R.Rec{k, row, same, last}))), M) == True{} : Bool}:
  match u:
    case True{}:
      ok
    case False{}:
      ok

def same_leak(u: Bool, -M: Nat, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, ok: {R.below(same, M) == True{} : Bool}) -> {R.below(R.Rec.same(R.Dec.r(R.rec.leak(u, R.Rk.leaks(k, row), same, last, R.Rec{k, row, same, last}))), M) == True{} : Bool}:
  match u:
    case True{}:
      ok
    case False{}:
      ok

# a round that ran: m < repeat, so whichever row it makes is below the cap
def same_kept(kept: Bool, +m: Nat, +b: Nat, pos: {R.below(0n, m) == True{} : Bool}, e: {R.below(m, b) == True{} : Bool}) -> {R.below(R.ran.same(kept, m), Nat.max(b, 1n)) == True{} : Bool}:
  match kept:
    case True{}:
      below_max(m, b, e)
    case False{}:
      one_below_max(m, b, pos, e)

def same_ran(+rc: R.RCfg, fresh: Bool, u: Bool, kept: Bool, +m: Nat, +h: Nat, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, pos: {R.below(0n, m) == True{} : Bool}, e: {R.below(m, R.RCfg.repeat(rc)) == fresh : Bool}, ok: {R.below(same, Nat.max(R.RCfg.repeat(rc), 1n)) == True{} : Bool}) -> {R.below(R.Rec.same(R.Dec.r(R.rec.ran(fresh, u, kept, m, h, R.Rk.loops(k, row), same, last, R.Rec{k, row, same, last}))), Nat.max(R.RCfg.repeat(rc), 1n)) == True{} : Bool}:
  match fresh u:
    case True{} u:
      same_kept(kept, m, R.RCfg.repeat(rc), pos, e)
    case False{} True{}:
      ok
    case False{} False{}:
      ok

def same_out(+rc: R.RCfg, o: R.Out, +k: R.Rk, +row: Nat, +same: Nat, +last: Nat, ok: {R.below(same, Nat.max(R.RCfg.repeat(rc), 1n)) == True{} : Bool}) -> {R.below(R.Rec.same(R.Dec.r(R.rec.go(rc, o, k, row, same, last))), Nat.max(R.RCfg.repeat(rc), 1n)) == True{} : Bool}:
  match o:
    case R.Long{}:
      same_long(R.below(R.Rk.longs(k, row), R.RCfg.long(rc)), Nat.max(R.RCfg.repeat(rc), 1n), k, row, same, last, ok)
    case R.Leak{rebuilt, +h, kept}:
      match rebuilt:
        case True{}:
          same_ran(rc, R.below(R.again(same, last, h), R.RCfg.repeat(rc)), R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), kept, R.again(same, last, h), h, k, row, same, last, again_pos(same, last, h), {==}, ok)
        case False{}:
          same_leak(R.below(R.Rk.leaks(k, row), R.RCfg.leak(rc)), Nat.max(R.RCfg.repeat(rc), 1n), k, row, same, last, ok)
    case R.Ran{+h, kept}:
      same_ran(rc, R.below(R.again(same, last, h), R.RCfg.repeat(rc)), R.below(R.Rk.loops(k, row), R.RCfg.redirect(rc)), kept, R.again(same, last, h), h, k, row, same, last, again_pos(same, last, h), {==}, ok)
    case R.Noted{}:
      ok
    case R.Said{}:
      zero_below_max(R.RCfg.repeat(rc))
    case R.Answer{}:
      zero_below_max(R.RCfg.repeat(rc))
    case R.Other{}:
      ok

def same_step(+rc: R.RCfg, o: R.Out, r: R.Rec, ok: {R.below(R.Rec.same(r), Nat.max(R.RCfg.repeat(rc), 1n)) == True{} : Bool}) -> {R.below(R.Rec.same(R.Dec.r(R.Rec.step(rc, o, r))), Nat.max(R.RCfg.repeat(rc), 1n)) == True{} : Bool}:
  match r:
    case R.Rec{k, row, same, last}:
      same_out(rc, o, k, row, same, last, ok)

def same_go(os: List<&2, R.Out>, +rc: R.RCfg, +r: R.Rec, ok: {R.below(R.Rec.same(r), Nat.max(R.RCfg.repeat(rc), 1n)) == True{} : Bool}) -> {R.below(R.Rec.same(R.Rec.go(os, rc, r)), Nat.max(R.RCfg.repeat(rc), 1n)) == True{} : Bool}:
  match os:
    case Nil{}:
      ok
    case +o <> rest:
      same_go(rest, rc, R.Dec.r(R.Rec.step(rc, o, r)), same_step(rc, o, r, ok))

def never_runs_a_repeat(+rc: R.RCfg, +os: List<&2, R.Out>) -> {R.below(R.Rec.same(R.Rec.run(rc, os)), Nat.max(R.RCfg.repeat(rc), 1n)) == True{} : Bool}:
  same_go(os, rc, R.Rec.init(), zero_below_max(R.RCfg.repeat(rc)))

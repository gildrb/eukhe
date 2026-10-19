# LAWS (H4.8): a stuck model gets a recovery. Each law is an open claim
# about the model in bend/run.bend; PROOF.bend proves them (as Rec.<law>)
# with the lemmas of bend/proof_recover.bend.

import Base
import ../bend/run.bend as Rn

# (H4.8) A stuck model gets a recovery, each with a cap
# -----------------------------------------------------
# docs/harness.md H4.8, the recoveries of bend/run.bend (Rec): a length
# stop while the model still reasons, tool calls leaked as text, the same
# tool calls with the same results round after round. Every reply is
# free, in any order. A Redo is a noted error, so its retry ends its
# request with a new note (H4.7); the laws of H4 hold for every reply, so
# they hold for the reply a recovery makes. A recovery does not depend on
# the retry policy: a note is a new request, not a transient error.

# LAW: a length stop with no answer under the cap (fewer than `long`
# length notes in a row) is retried with the next length note
law rec_length_retries_with_a_note:
  for +rc: Rn.RCfg
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for under: {Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)) == True{} : Bool}
  {Rn.Rec.step(rc, Rn.Long{}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Longs{}, 1n+Rn.Rk.longs(k, row), same, last}} : Rn.Dec}

# LAW: after `long` length notes in a row, a length stop fails the run
law rec_length_gives_up:
  for +rc: Rn.RCfg
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for over: {Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)) == False{} : Bool}
  {Rn.Dec.act(Rn.Rec.step(rc, Rn.Long{}, Rn.Rec{k, row, same, last})) == Rn.Quit{} : Rn.Act}

# LAW: leaked calls that every parse and name an offered tool are rebuilt:
# the run reads them as the same calls made as tool calls
law rec_leak_rebuilt_is_calls:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for r: Rn.Rec
  {Rn.Rec.step(rc, Rn.Leak{True{}, h, kept}, r) == Rn.Rec.step(rc, Rn.Ran{h, kept}, r) : Rn.Dec}

# LAW: leaked calls that were not rebuilt, under the cap, are retried with
# the next leak note
law rec_leak_retries_with_a_note:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for under: {Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)) == True{} : Bool}
  {Rn.Rec.step(rc, Rn.Leak{False{}, h, kept}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Leaks{}, 1n+Rn.Rk.leaks(k, row), same, last}} : Rn.Dec}

# LAW: after `leak` leak notes in a row, the reply answers as text
law rec_leak_stands:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for over: {Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)) == False{} : Bool}
  {Rn.Dec.act(Rn.Rec.step(rc, Rn.Leak{False{}, h, kept}, Rn.Rec{k, row, same, last})) == Rn.Stand{} : Rn.Act}

# LAW: tool calls that make fewer than `repeat` rounds in a row run: the
# recoveries never stop a call that is not a repeat. The rounds in a row
# grow when the results are those of the last round; when the results
# change (a poll of a job that makes progress), a new row of 1 starts
law rec_calls_run:
  for +rc: Rn.RCfg
  for +h: Nat
  for +kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for fresh: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == True{} : Bool}
  {Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Exec{}, Rn.Rec{Rn.Free{}, 0n, Rn.ran.same(kept, Rn.again(same, last, h)), h}} : Rn.Dec}

# LAW: tool calls that would make `repeat` rounds in a row with the same
# results never run
law rec_repeat_never_runs:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}
  {Rn.Act.runs(Rn.Dec.act(Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}))) == False{} : Bool}

# LAW: such a repeat, under the cap, is retried with the next redirect
# note
law rec_repeat_redirects:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}
  for under: {Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)) == True{} : Bool}
  {Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Loops{}, 1n+Rn.Rk.loops(k, row), same, last}} : Rn.Dec}

# LAW: after `redirect` redirect notes in a row, a repeat fails the run
law rec_repeat_gives_up:
  for +rc: Rn.RCfg
  for +h: Nat
  for kept: Bool
  for +k: Rn.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}
  for over: {Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)) == False{} : Bool}
  {Rn.Dec.act(Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last})) == Rn.Quit{} : Rn.Act}

# LAW: a user message ends the row: after it, no call is a repeat of a
# call before it
law rec_user_breaks_the_row:
  for +rc: Rn.RCfg
  for +k: Rn.Rk
  for +row: Nat
  for same: Nat
  for +last: Nat
  {Rn.Dec.r(Rn.Rec.step(rc, Rn.Said{}, Rn.Rec{k, row, same, last})) == Rn.Rec{k, row, 0n, last} : Rn.Rec}

# LAW: after any replies, the notes of a recovery in a row are at most
# its cap: every recovery stops at its cap
law rec_notes_capped:
  for +rc: Rn.RCfg
  for +os: List<&2, Rn.Out>
  {Rn.Rec.capped(rc, Rn.Rec.run(rc, os)) == True{} : Bool}

# LAW: after any replies, the run has not run the same calls with the
# same results max(repeat, 1) rounds in a row. This replaces the loop
# guard of H4.3 (a run failed after LOOP_ROUNDS = 6 such rounds): it is
# stronger, as no such row ever reaches `repeat` (5) rounds
law rec_never_runs_a_repeat:
  for +rc: Rn.RCfg
  for +os: List<&2, Rn.Out>
  {Rn.below(Rn.Rec.same(Rn.Rec.run(rc, os)), Nat.max(Rn.RCfg.repeat(rc), 1n)) == True{} : Bool}

# LAW: the harness never just watches a stuck model: a stuck reply (a
# length stop with no answer, leaked tool calls, tool calls) always gets
# an act that does something: its calls run (no repeat), a retry with a
# note, an answer, or the end of the run. It is never passed on as it is
law rec_stuck_gets_help:
  for +rc: Rn.RCfg
  for o: Rn.Out
  for r: Rn.Rec
  {Bool.or(Bool.not(Rn.Out.stuck(o)), Rn.Act.helps(Rn.Dec.act(Rn.Rec.step(rc, o, r)))) == True{} : Bool}

# LAW: a recovery's retry is a noted error, so its request ends with the
# note of the next attempt (run_cut_names_the_request): it never sends
# the request again (run_retry_sends_a_new_request)
law rec_redo_is_noted:
  for -pass: Rn.Reply
  {Rn.Act.reply(Rn.Redo{}, pass) == Rn.Error{False{}, True{}} : Rn.Reply}

# LAW: a recovery at its cap fails the run on the model, at once
law rec_quit_fails:
  for +cfg: Rn.Cfg
  for -pass: Rn.Reply
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {Rn.call(cfg, Rn.Act.reply(Rn.Quit{}, pass), r, c, a, n, p) == Rn.St{Rn.Failed{Rn.Model{}}, r, c, a, n, p} : Rn.St}

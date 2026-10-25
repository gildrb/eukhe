# eukhe: the proof of LAW tiny_run_entry_history
#
# PROOF: the open is the spec's (tiny_run_entry_open). Then by induction
# on the outcomes: each spelled outcome moves the entry as the spec's
# table and answers its spelled reply (tiny_run_entry_answers); the
# table is the model's step (tiny_run_step_is_model), so the entry's
# next state is the model's run after the outcome, and the rest follows.

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_run.bend as FTr
import ../../laws/tiny/run.bend as TinyRun
import ./tiny_run_entry_open.bend as PTinyRunEntryOpen
import ./tiny_run_entry_answers.bend as PTinyRunEntryAnswers
import ./tiny_run_step_is_model.bend as PTinyRunStepIsModel
import ./base.bend as LA

def trh.model(x: Tn.Run, +s: Tn.Seen) -> {Tn.step_run(x, s) == TinyRun.sp_step_r(x, s) : Tn.Run & Tn.Do}:
  match x:
    case Tn.Run{+m, +ph}:
      TinyRun.tiny_run_step_is_model(m, ph, s)

def trh.go(ss: List<&2, Tn.Seen>, r: Tn.Run & Tn.Do, fs: {TinyRun.sp_all_fit(ss) == True{} : Bool}) -> {TinyRun.tr_feed(ss, TinyRun.sp_reply(r)) == TinyRun.sp_w_dos(TinyRun.tr_replies(ss, r)) : List<&2, String>}:
  match ss:
    case Nil{}:
      (x, d) = r
      {==}
    case +s <> +t:
      (+x, +d) = r
      +f2 = fs
      %Equal.sym(FTr.St & String, FTr.step(FTr.Live{x}, TinyRun.sp_w_seen(s, "")), TinyRun.sp_reply(TinyRun.sp_step_r(x, s)), TinyRun.tiny_run_entry_answers(x, s, LA.tiny.pn.and_l(TinyRun.sp_fit_seen(s), TinyRun.sp_all_fit(t), f2))) : {TinyRun.sp_w_do(d) <> TinyRun.tr_feed(t, _) == TinyRun.sp_w_do(d) <> TinyRun.sp_w_dos(TinyRun.tr_replies(t, Tn.step_run(x, s))) : List<&2, String>}
      %trh.model(x, s) : {TinyRun.sp_w_do(d) <> TinyRun.tr_feed(t, TinyRun.sp_reply(_)) == TinyRun.sp_w_do(d) <> TinyRun.sp_w_dos(TinyRun.tr_replies(t, Tn.step_run(x, s))) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, z => TinyRun.sp_w_do(d) <> z, TinyRun.tr_feed(t, TinyRun.sp_reply(Tn.step_run(x, s))), TinyRun.sp_w_dos(TinyRun.tr_replies(t, Tn.step_run(x, s))), trh.go(t, Tn.step_run(x, s), LA.tiny.pn.and_r(TinyRun.sp_fit_seen(s), TinyRun.sp_all_fit(t), f2)))

def TinyRun.tiny_run_entry_history(o, ss, fo, fs):
  %Equal.sym(FTr.St & String, FTr.open(TinyRun.sp_w_open(o, "")), TinyRun.sp_reply(TinyRun.sp_open(o)), TinyRun.tiny_run_entry_open(o, fo)) : {TinyRun.tr_feed(ss, _) == TinyRun.sp_w_dos(TinyRun.tr_replies(ss, TinyRun.sp_open(o))) : List<&2, String>}
  trh.go(ss, TinyRun.sp_open(o), fs)

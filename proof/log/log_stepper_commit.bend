# eukhe: the proof of LAW log_stepper_commit
#
# The sidecar entries read back (pe.rt), nothing is left, and the entry
# spells the plan's steps as the spec does (pl.answer: the act codecs
# agree step by step).

import Base
import ../../bend/log.bend as Lr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/log.bend as Log
import ./base.bend as LA

def pl.act(a: Lr.Act, +s: String) -> {FLg.put_act(a, s) == Log.log_spell_act(a, s) : String}:
  match a:
    case Lr.FlushParent{}:
      {==}
    case Lr.AppendSide{i}:
      {==}
    case Lr.FlushSide{i}:
      {==}
    case Lr.FlushDir{}:
      {==}
    case Lr.AppendMain{}:
      {==}
    case Lr.FlushMain{}:
      {==}
    case Lr.Ack{}:
      {==}

def pl.step(+a: Lr.Act, r: Nat & String) -> {Wr.put_list.step(~Lr.Act, ~FLg.put_act, a, r) == Wr.put_list.step(~Lr.Act, ~Log.log_spell_act, a, r) : Nat & String}:
  (n, +s) = r
  %pl.act(a, s) : {(1n+n, FLg.put_act(a, s)) == (1n+n, _) : Nat & String}
  {==}

def pl.go(acts: List<&2, Lr.Act>, +rest: String) -> {Wr.put_list.go(~Lr.Act, ~FLg.put_act, acts, rest) == Wr.put_list.go(~Lr.Act, ~Log.log_spell_act, acts, rest) : Nat & String}:
  match acts:
    case Nil{}:
      {==}
    case +a <> +t:
      %pl.go(t, rest) : {Wr.put_list.step(~Lr.Act, ~FLg.put_act, a, Wr.put_list.go(~Lr.Act, ~FLg.put_act, t, rest)) == Wr.put_list.step(~Lr.Act, ~Log.log_spell_act, a, _) : Nat & String}
      pl.step(a, Wr.put_list.go(~Lr.Act, ~FLg.put_act, t, rest))

def pl.answer(p: Lr.Plan) -> {FLg.reply(p) == Log.log_answer(p) : FLg.St & String}:
  match p:
    case Lr.Plan{s, +acts}:
      %pl.go(acts, "") : {(FLg.Running{s}, Wr.put_list.fin(Wr.put_list.go(~Lr.Act, ~FLg.put_act, acts, ""))) == (FLg.Running{s}, Wr.put_list.fin(_)) : FLg.St & String}
      {==}

def Log.log_stepper_commit(s, ds, fits):
  %Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, Log.log_spell_sides(ds)), Wr.Got{ds, ""}, LA.pe.rt(ds, "", fits)) : {FLg.step.go(s, _) == Log.log_answer(Lr.Store.commit(s, ds)) : FLg.St & String}
  pl.answer(Lr.Store.commit(s, ds))

# eukhe: the proof of LAW cron_beats_decide_exact

import Base
import ../../bend/cron_store.bend as CS
import ../../bend/cron_beats.bend as CB
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_beats.bend as CronBeats
import ../cron_store/cron_take_exact.bend as PTake
import ../cron_store/cron_recover_exact.bend as PRecover
import ../cron_store/cron_finish_exact.bend as PFinish
import ../cron_store/cron_cancel_exact.bend as PCancel
import ../cron_store/cron_resume_exact.bend as PResume
import ../cron_store/cron_halt_exact.bend as PHalt
import ../cron_store/cron_edit_exact.bend as PEdit

# Each decision of the code is its spec (the cron_*_exact laws of
# laws/cron_store.bend); each answer, applied, writes what it names; the
# i-th record takes it and the others stay.

# Answers
# -------

def de.next(n: CS.Next, +r: Nat) -> {CB.next_at(n, r) == CronBeats.next_run_spec(n, r) : Maybe<&2, Nat>}:
  match n:
    case CS.NNone{}:
      {==}
    case CS.NAt{ms}:
      {==}
    case CS.NRoll{}:
      {==}

def de.took(t: CS.Took, +r: Nat, f: CS.Fact) -> {CB.took(t, r, f) == CronBeats.written_spec(CronBeats.took_sets_spec(t, r), f) : CS.Fact}:
  match t:
    case CS.Keep{}:
      {==}
    case CS.Roll{+n}:
      match f:
        case CS.Fact{st, p, nx, k}:
          %de.next(n, r) : {CS.Fact{st, p, CB.next_at(n, r), k} == CS.Fact{st, p, _, k} : CS.Fact}
          {==}
    case CS.Claimed{+n}:
      match f:
        case CS.Fact{st, p, nx, k}:
          %de.next(n, r) : {CS.Fact{st, p, CB.next_at(n, r), k} == CS.Fact{st, p, _, k} : CS.Fact}
          {==}

def de.back(b: CS.Back, f: CS.Fact) -> {CB.back(b, f) == CronBeats.written_spec(CronBeats.back_sets_spec(b), f) : CS.Fact}:
  match b:
    case CS.Kept{}:
      {==}
    case CS.Interrupted{st2, nx2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          {==}

def de.fin(x: CS.Fin, +r: Nat, f: CS.Fact) -> {CB.fin(x, r, f) == CronBeats.written_spec(CronBeats.fin_sets_spec(x, r), f) : CS.Fact}:
  match x:
    case CS.Untouched{}:
      {==}
    case CS.Ran{st2, +n, k2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          %de.next(n, r) : {CS.Fact{st2, p, CB.next_at(n, r), k2} == CS.Fact{st2, p, _, k2} : CS.Fact}
          {==}
    case CS.Skipped{st2, +n, k2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          %de.next(n, r) : {CS.Fact{st2, p, CB.next_at(n, r), k2} == CS.Fact{st2, p, _, k2} : CS.Fact}
          {==}

def de.cut(x: CS.Cut, f: CS.Fact) -> {CB.cut(x, f) == CronBeats.written_spec(CronBeats.cut_sets_spec(x), f) : CS.Fact}:
  match x:
    case CS.Same{}:
      {==}
    case CS.Cut{st2, nx2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          {==}

def de.again(x: CS.Again, +r: Nat, f: CS.Fact) -> {CB.again(x, r, f) == CronBeats.written_spec(CronBeats.again_sets_spec(x, r), f) : CS.Fact}:
  match x:
    case CS.Resumed{st2, +n, k2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          %de.next(n, r) : {CS.Fact{st2, p, CB.next_at(n, r), k2} == CS.Fact{st2, p, _, k2} : CS.Fact}
          {==}
    case CS.Ended{}:
      {==}
    case CS.NotRecurring{}:
      {==}

def de.edited(x: CS.Edit, f: CS.Fact) -> {CB.edited(x, f) == CronBeats.written_spec(CronBeats.edit_sets_spec(x), f) : CS.Fact}:
  match x:
    case CS.Locked{}:
      {==}
    case CS.Edited{st2, nx2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          {==}

# Decisions
# ---------

def de.apply(op: CB.Op, +f: CS.Fact) -> {CB.apply(op, f) == CronBeats.written_spec(CronBeats.sets_spec(op, f), f) : CS.Fact}:
  match op:
    case CB.OTake{+c, +d, +n, +r}:
      %CronStore.cron_take_exact(f, c, d, n) : {CB.took(CS.take(f, c, d, n), r, f) == CronBeats.written_spec(CronBeats.took_sets_spec(_, r), f) : CS.Fact}
      de.took(CS.take(f, c, d, n), r, f)
    case CB.ORecover{+c}:
      %CronStore.cron_recover_exact(f, c) : {CB.back(CS.recover(f, c), f) == CronBeats.written_spec(CronBeats.back_sets_spec(_), f) : CS.Fact}
      de.back(CS.recover(f, c), f)
    case CB.OFinish{+u, +a, +b, +n, +r}:
      %CronStore.cron_finish_exact(u, f, a, b, n) : {CB.fin(CS.finish(u, f, a, b, n), r, f) == CronBeats.written_spec(CronBeats.fin_sets_spec(_, r), f) : CS.Fact}
      de.fin(CS.finish(u, f, a, b, n), r, f)
    case CB.OCancel{}:
      %CronStore.cron_cancel_exact(f) : {CB.cut(CS.cancel(f), f) == CronBeats.written_spec(CronBeats.cut_sets_spec(_), f) : CS.Fact}
      de.cut(CS.cancel(f), f)
    case CB.OResume{+n, +r}:
      %CronStore.cron_resume_exact(f, n) : {CB.again(CS.resume(f, n), r, f) == CronBeats.written_spec(CronBeats.again_sets_spec(_, r), f) : CS.Fact}
      de.again(CS.resume(f, n), r, f)
    case CB.OHalt{+how}:
      %CronStore.cron_halt_exact(f, how) : {CB.cut(CS.halt(f, how), f) == CronBeats.written_spec(CronBeats.cut_sets_spec(_), f) : CS.Fact}
      de.cut(CS.halt(f, how), f)
    case CB.OEdit{+at}:
      %CronStore.cron_edit_exact(f, at) : {CB.edited(CS.edit(f, at), f) == CronBeats.written_spec(CronBeats.edit_sets_spec(_), f) : CS.Fact}
      de.edited(CS.edit(f, at), f)

# CronBeats

def CronBeats.cron_beats_decide_exact(i, op, rs):
  match i:
    case 0n:
      match rs:
        case Nil{}:
          {==}
        case r <> t:
          match r:
            case CB.Row{s, fl, hb, +f}:
              %de.apply(op, f) : {CB.Row{s, fl, hb, CB.apply(op, f)} <> t == CB.Row{s, fl, hb, _} <> t : List<&2, CB.Row>}
              {==}
    case 1n+q:
      match rs:
        case Nil{}:
          {==}
        case +r <> t:
          %CronBeats.cron_beats_decide_exact(q, op, t) : {r <> CB.on(q, op, t) == r <> _ : List<&2, CB.Row>}
          {==}

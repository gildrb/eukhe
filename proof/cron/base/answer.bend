# eukhe: lemmas the proofs of area cron share: the model's pause in
# minutes is the spec's table, the entry's reply writers write what the
# laws' spellers write, and the entry's answer to every request is the
# laws' reply (each decision being its spec: the cron_store laws).

import Base
import ../../../bend/cron.bend as Cr
import ../../../bend/cron_store.bend as CS
import ../../../bend/ffi_cron.bend as FC
import ../../../bend/wire.bend as Wr
import ../../../laws/cron.bend as Cron
import ../../../laws/cron_store.bend as CronStore
import ../../cron_store/cron_take_exact.bend as PX0
import ../../cron_store/cron_clear_exact.bend as PX1
import ../../cron_store/cron_recover_exact.bend as PX2
import ../../cron_store/cron_finish_exact.bend as PX3
import ../../cron_store/cron_cancel_exact.bend as PX4
import ../../cron_store/cron_resume_exact.bend as PX5

# Decisions
# ---------

def creq.delay(k: Nat) -> {Cr.delay(k) == CronStore.pause_min_spec(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n+r:
      {==}

# Writers
# -------

def crw.status(st: Cr.Status, rest: String) -> {FC.put_status(st, rest) == Cron.spell_status(st, rest) : String}:
  match st:
    case Cr.Active{}:
      {==}
    case Cr.Paused{}:
      {==}
    case Cr.Finished{}:
      {==}
    case Cr.Cancelled{}:
      {==}

def crw.mnat(m: Maybe<&2, Nat>, rest: String) -> {FC.put_mnat(m, rest) == Cron.spell_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def crw.next(n: CS.Next, rest: String) -> {FC.put_next(n, rest) == Cron.spell_next(n, rest) : String}:
  match n:
    case CS.NNone{}:
      {==}
    case CS.NAt{x}:
      {==}
    case CS.NRoll{}:
      {==}

def crw.took(t: CS.Took, +rest: String) -> {FC.put_took(t, rest) == Cron.spell_took(t, rest) : String}:
  match t:
    case CS.Keep{}:
      {==}
    case CS.Roll{+n}:
      %crw.next(n, rest) : {Wr.put_nat(1n, FC.put_next(n, rest)) == Wr.put_nat(1n, _) : String}
      {==}
    case CS.Claimed{+n}:
      %crw.next(n, rest) : {Wr.put_nat(2n, FC.put_next(n, rest)) == Wr.put_nat(2n, _) : String}
      {==}

def crw.back(b: CS.Back, +rest: String) -> {FC.put_back(b, rest) == Cron.spell_back(b, rest) : String}:
  match b:
    case CS.Kept{}:
      {==}
    case CS.Interrupted{+st, +m}:
      %crw.mnat(m, rest) : {Wr.put_nat(1n, FC.put_status(st, FC.put_mnat(m, rest))) == Wr.put_nat(1n, Cron.spell_status(st, _)) : String}
      %crw.status(st, FC.put_mnat(m, rest)) : {Wr.put_nat(1n, FC.put_status(st, FC.put_mnat(m, rest))) == Wr.put_nat(1n, _) : String}
      {==}

# a status, a next run and a count, as both write them
def crw.snk(+st: Cr.Status, +n: CS.Next, +k: Nat, +rest: String) -> {FC.put_status(st, FC.put_next(n, Wr.put_nat(k, rest))) == Cron.spell_status(st, Cron.spell_next(n, Wr.put_nat(k, rest))) : String}:
  %crw.next(n, Wr.put_nat(k, rest)) : {FC.put_status(st, FC.put_next(n, Wr.put_nat(k, rest))) == Cron.spell_status(st, _) : String}
  crw.status(st, FC.put_next(n, Wr.put_nat(k, rest)))

def crw.fin(x: CS.Fin, +rest: String) -> {FC.put_fin(x, rest) == Cron.spell_fin(x, rest) : String}:
  match x:
    case CS.Untouched{}:
      {==}
    case CS.Ran{+st, +n, +k}:
      %crw.snk(st, n, k, rest) : {Wr.put_nat(1n, FC.put_status(st, FC.put_next(n, Wr.put_nat(k, rest)))) == Wr.put_nat(1n, _) : String}
      {==}
    case CS.Skipped{+st, +n, +k}:
      %crw.snk(st, n, k, rest) : {Wr.put_nat(2n, FC.put_status(st, FC.put_next(n, Wr.put_nat(k, rest)))) == Wr.put_nat(2n, _) : String}
      {==}

def crw.cut(x: CS.Cut, +rest: String) -> {FC.put_cut(x, rest) == Cron.spell_cut(x, rest) : String}:
  match x:
    case CS.Same{}:
      {==}
    case CS.Cut{+st, +m}:
      %crw.mnat(m, rest) : {Wr.put_nat(1n, FC.put_status(st, FC.put_mnat(m, rest))) == Wr.put_nat(1n, Cron.spell_status(st, _)) : String}
      %crw.status(st, FC.put_mnat(m, rest)) : {Wr.put_nat(1n, FC.put_status(st, FC.put_mnat(m, rest))) == Wr.put_nat(1n, _) : String}
      {==}

def crw.again(x: CS.Again, +rest: String) -> {FC.put_again(x, rest) == Cron.spell_again(x, rest) : String}:
  match x:
    case CS.Resumed{+st, +n, +k}:
      %crw.snk(st, n, k, rest) : {Wr.put_nat(0n, FC.put_status(st, FC.put_next(n, Wr.put_nat(k, rest)))) == Wr.put_nat(0n, _) : String}
      {==}
    case CS.Ended{}:
      {==}
    case CS.NotRecurring{}:
      {==}

# Answers
# -------

# the entry's answer to every request is the laws' reply to it
def cran.answer(a: CS.Ask) -> {FC.answer(a) == Cron.spell_answer(a) : String}:
  match a:
    case CS.AskTake{+f, +c, +d, +n}:
      %CronStore.cron_take_exact(f, c, d, n) : {FC.put_took(CS.take(f, c, d, n), "") == Cron.spell_took(_, "") : String}
      crw.took(CS.take(f, c, d, n), "")
    case CS.AskClear{+w}:
      %CronStore.cron_clear_exact(w) : {Wr.put_bool(CS.clear(w), "") == Wr.put_bool(_, "") : String}
      {==}
    case CS.AskRecover{+f, +c}:
      %CronStore.cron_recover_exact(f, c) : {FC.put_back(CS.recover(f, c), "") == Cron.spell_back(_, "") : String}
      crw.back(CS.recover(f, c), "")
    case CS.AskFinish{+f, +r, +b, +n}:
      %CronStore.cron_finish_exact(60000n, f, r, b, n) : {FC.put_fin(CS.finish(60000n, f, r, b, n), "") == Cron.spell_fin(_, "") : String}
      crw.fin(CS.finish(60000n, f, r, b, n), "")
    case CS.AskCancel{+f}:
      %CronStore.cron_cancel_exact(f) : {FC.put_cut(CS.cancel(f), "") == Cron.spell_cut(_, "") : String}
      crw.cut(CS.cancel(f), "")
    case CS.AskResume{+f, +n}:
      %CronStore.cron_resume_exact(f, n) : {FC.put_again(CS.resume(f, n), "") == Cron.spell_again(_, "") : String}
      crw.again(CS.resume(f, n), "")

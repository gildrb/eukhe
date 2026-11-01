# eukhe: lemmas the proofs of area cron_serve share: the entry's writers
# of the per-job decisions (bend/ffi_cron_serve.bend) write what the laws'
# spellers write.

import Base
import ../../../bend/cron.bend as Cr
import ../../../bend/cron_store.bend as CS
import ../../../bend/ffi_cron_serve.bend as FC
import ../../../bend/wire.bend as Wr
import ../../../laws/cron.bend as Cron

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

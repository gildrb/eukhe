# eukhe: lemmas of the cron_beats proofs: a per-job decision on the i-th
# record (CB.on) is the spec's decide_spec. Each decision of the code is
# its spec (proof/cron_store/base.bend); each answer, applied, writes what
# it names; the i-th record takes it and the others stay.

import Base
import ../../bend/cron_store.bend as CS
import ../../bend/cron_beats.bend as CB
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_beats.bend as CronBeats
import ../cron_store/base.bend as LCs

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

def de.back(b: CS.Back, +at: Nat, f: CS.Fact) -> {CB.back(b, at, f) == CronBeats.written_spec(CronBeats.back_sets_spec(b, at), f) : CS.Fact}:
  match b:
    case CS.Kept{}:
      {==}
    case CS.Interrupted{st2, nx2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          {==}
    case CS.Refire{}:
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
      %LCs.cx.take(f, c, d, n) : {CB.took(CS.take(f, c, d, n), r, f) == CronBeats.written_spec(CronBeats.took_sets_spec(_, r), f) : CS.Fact}
      de.took(CS.take(f, c, d, n), r, f)
    case CB.ORecover{+c, +at}:
      %LCs.cx.recover(f, c) : {CB.back(CS.recover(f, c), at, f) == CronBeats.written_spec(CronBeats.back_sets_spec(_, at), f) : CS.Fact}
      de.back(CS.recover(f, c), at, f)
    case CB.OFinish{+u, +a, +b, +n, +r}:
      %LCs.cx.finish(u, f, a, b, n) : {CB.fin(CS.finish(u, f, a, b, n), r, f) == CronBeats.written_spec(CronBeats.fin_sets_spec(_, r), f) : CS.Fact}
      de.fin(CS.finish(u, f, a, b, n), r, f)
    case CB.OCancel{}:
      %LCs.cx.cancel(f) : {CB.cut(CS.cancel(f), f) == CronBeats.written_spec(CronBeats.cut_sets_spec(_), f) : CS.Fact}
      de.cut(CS.cancel(f), f)
    case CB.OResume{+n, +r}:
      %LCs.cx.resume(f, n) : {CB.again(CS.resume(f, n), r, f) == CronBeats.written_spec(CronBeats.again_sets_spec(_, r), f) : CS.Fact}
      de.again(CS.resume(f, n), r, f)
    case CB.OHalt{+how}:
      %LCs.cx.halt(f, how) : {CB.cut(CS.halt(f, how), f) == CronBeats.written_spec(CronBeats.cut_sets_spec(_), f) : CS.Fact}
      de.cut(CS.halt(f, how), f)
    case CB.OEdit{+at}:
      %LCs.cx.edit(f, at) : {CB.edited(CS.edit(f, at), f) == CronBeats.written_spec(CronBeats.edit_sets_spec(_), f) : CS.Fact}
      de.edited(CS.edit(f, at), f)

# The i-th record
# --------------

def de.on(i: Nat, +op: CB.Op, rs: List<&2, CB.Row>) -> {CB.on(i, op, rs) == CronBeats.decide_spec(rs, i, op) : List<&2, CB.Row>}:
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
          %de.on(q, op, t) : {r <> CB.on(q, op, t) == r <> _ : List<&2, CB.Row>}
          {==}

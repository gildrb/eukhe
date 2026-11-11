# eukhe: lemmas the cron proofs share: each per-job decision of the code
# that runs (bend/cron_store.bend) is its spec (laws/cron_store.bend), by
# a case split on the facts it reads. The laws that state the decisions
# through the entry (cron_entry_answers, cron_file_entry_answers), on every
# clock unit (cron_file_finish_exact) and record by record
# (cron_beats_step_exact) are proven with them.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore

# A claim pass

def cx.take_due(b: Bool, c: Bool, p: CS.Plan, +n: Nat) -> {CS.take.due(b, c, p, n) == CronStore.take_spec.due(b, c, p, n) : CS.Took}:
  match b c p:
    case False{} _ _:
      {==}
    case True{} True{} CS.POnce{}:
      {==}
    case True{} True{} CS.PEvery{ms}:
      {==}
    case True{} True{} CS.PRule{}:
      {==}
    case True{} False{} CS.POnce{}:
      {==}
    case True{} False{} CS.PEvery{ms}:
      {==}
    case True{} False{} CS.PRule{}:
      {==}

def cx.take(f: CS.Fact, c: Bool, +d: Nat, +n: Nat) -> {CS.take(f, c, d, n) == CronStore.take_spec(f, c, d, n) : CS.Took}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          match nx:
            case None{}:
              {==}
            case Some{+m}:
              cx.take_due(Nat.is_le(m, d), c, p, n)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

# A claim's verdict

def cx.clear(w: CS.Who) -> {CS.clear(w) == CronStore.clear_spec(w) : Bool}:
  match w:
    case CS.Mine{r}:
      match r:
        case True{}:
          {==}
        case False{}:
          {==}
    case CS.Theirs{d}:
      {==}

# A recovery

def cx.recover(f: CS.Fact, c: Bool) -> {CS.recover(f, c) == CronStore.recover_spec(f, c) : CS.Back}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st p:
        case Cr.Active{} CS.POnce{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cr.Active{} CS.PEvery{ms}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cr.Active{} CS.PRule{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cr.Paused{} _:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cr.Finished{} _:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cr.Cancelled{} _:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}

# The finish step: a failure under the cap waits the model's pause (Cr.delay, the spec's table) after the later of the next run and the pause's end (Cr.later, the spec's)

def cx.delay(k: Nat) -> {Cr.delay(k) == CronStore.pause_min_spec(k) : Nat}:
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

def cx.later_pick(b: Bool, n: Nat, w: Nat) -> {Cr.later.pick(b, n, w) == CronStore.later_spec.pick(b, n, w) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cx.later(nx: Maybe<&2, Nat>, +w: Nat) -> {Cr.later(nx, w) == CronStore.later_spec(nx, w) : Nat}:
  match nx:
    case None{}:
      {==}
    case Some{+n}:
      cx.later_pick(Nat.is_lt(n, w), n, w)

def cx.fail(b: Bool, +now: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +u: Nat) -> {CS.finish.fail(b, now, nx, k, u) == CronStore.finish_spec.fail(b, nx, k, now, u) : CS.Fin}:
  match b:
    case True{}:
      %cx.delay(k) : {CS.Ran{Cr.Active{}, CS.NAt{Cr.later(nx, Nat.add(now, Nat.mul(Cr.delay(k), u)))}, k} == CS.Ran{Cr.Active{}, CS.NAt{CronStore.later_spec(nx, Nat.add(now, Nat.mul(_, u)))}, k} : CS.Fin}
      %cx.later(nx, Nat.add(now, Nat.mul(Cr.delay(k), u))) : {CS.Ran{Cr.Active{}, CS.NAt{Cr.later(nx, Nat.add(now, Nat.mul(Cr.delay(k), u)))}, k} == CS.Ran{Cr.Active{}, CS.NAt{_}, k} : CS.Fin}
      {==}
    case False{}:
      {==}

def cx.finish_on(failed: Bool, ran: Bool, p: CS.Plan, nx: Maybe<&2, Nat>, +k: Nat, +now: Nat, +u: Nat) -> {CS.finish.active(CS.outcome(failed, ran), p, nx, k, now, u) == CronStore.finish_spec.on(failed, ran, CronStore.once_spec(p), p, nx, k, now, u) : CS.Fin}:
  match failed ran p:
    case True{} _ CS.POnce{}:
      {==}
    case True{} _ CS.PEvery{ms}:
      cx.fail(Nat.is_lt(1n+k, 8n), now, nx, 1n+k, u)
    case True{} _ CS.PRule{}:
      cx.fail(Nat.is_lt(1n+k, 8n), now, nx, 1n+k, u)
    case False{} True{} CS.POnce{}:
      {==}
    case False{} True{} CS.PEvery{ms}:
      match nx:
        case None{}:
          {==}
        case Some{m}:
          {==}
    case False{} True{} CS.PRule{}:
      match nx:
        case None{}:
          {==}
        case Some{m}:
          {==}
    case False{} False{} CS.POnce{}:
      {==}
    case False{} False{} CS.PEvery{ms}:
      {==}
    case False{} False{} CS.PRule{}:
      {==}

def cx.finish(+u: Nat, f: CS.Fact, ran: Bool, failed: Bool, +now: Nat) -> {CS.finish(u, f, ran, failed, now) == CronStore.finish_spec(u, f, ran, failed, now) : CS.Fin}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          cx.finish_on(failed, ran, p, nx, k, now, u)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

# A cancel

def cx.cancel(f: CS.Fact) -> {CS.cancel(f) == CronStore.cancel_spec(f) : CS.Cut}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

# A resume

def cx.resume_plan(p: CS.Plan, +now: Nat) -> {CS.resume.plan(p, now) == CronStore.resume_spec.plan(p, now) : CS.Again}:
  match p:
    case CS.POnce{}:
      {==}
    case CS.PEvery{ms}:
      {==}
    case CS.PRule{}:
      {==}

def cx.resume(f: CS.Fact, +now: Nat) -> {CS.resume(f, now) == CronStore.resume_spec(f, now) : CS.Again}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          cx.resume_plan(p, now)
        case Cr.Paused{}:
          cx.resume_plan(p, now)
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

# A pause, a stop, a delete

def cx.halt_st(h: CS.Halt, st: Cr.Status, p: CS.Plan, nx: Maybe<&2, Nat>, k: Nat) -> {CS.halt(CS.Fact{st, p, nx, k}, h) == CronStore.halt_spec(CS.Fact{st, p, nx, k}, h) : CS.Cut}:
  match h:
    case CS.HPause{}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}
    case CS.HStop{}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}
    case CS.HDelete{}:
      {==}

def cx.halt(f: CS.Fact, h: CS.Halt) -> {CS.halt(f, h) == CronStore.halt_spec(f, h) : CS.Cut}:
  match f:
    case CS.Fact{st, p, nx, k}:
      cx.halt_st(h, st, p, nx, k)

# An edit

def cx.edit(f: CS.Fact, at: Maybe<&2, Nat>) -> {CS.edit(f, at) == CronStore.edit_spec(f, at) : CS.Edit}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          match at:
            case None{}:
              {==}
            case Some{a}:
              {==}
        case Cr.Paused{}:
          match at:
            case None{}:
              {==}
            case Some{a}:
              {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

# A new job

def cx.make(at: Nat) -> {CS.make(at) == CronStore.make_spec(at) : CS.Made}:
  {==}

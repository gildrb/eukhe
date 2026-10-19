# proof_kernel_local: the K1 laws (laws/kernel_local.bend) of the kernel
# setup model in bend/kernel_local.bend.
#
# A setup's plan is a fixed list for each venv found and each setup, so
# the setup laws hold by computation in every case. The tool laws read
# the answer: another tool runs whatever the kernel, and a failed setup
# of a venv that is not current is Missing. The sweep laws go by
# induction on the files: each file is kept exactly when it is not a
# leftover of a dead attempt.

import Base
import ./kernel_local.bend as KL

# Logic
# -----

def pk.KD(k: KL.Kernel, u: Type, m: Type) -> Type:
  match k:
    case KL.Up{}:
      u
    case KL.Missing{}:
      m

def pk.up_missing(-A: Type, e: {KL.Up{} == KL.Missing{} : KL.Kernel}) -> A:
  %e : pk.KD(_, Unit, A)
  Unit{}

def pk.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pk.false_true(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pk.BD(_, A, Unit)
  Unit{}

# The setup
# ---------

def pk.session_never_downloads(f: KL.Found) -> {KL.acts.fetching(KL.plan(f, KL.Local{})) == False{} : Bool}:
  match f:
    case KL.Current{}:
      {==}
    case KL.Skills{}:
      {==}
    case KL.Stale{}:
      {==}

def pk.download_only_on_install(f: KL.Found, s: KL.Setup, fetches: {KL.acts.fetching(KL.plan(f, s)) == True{} : Bool}) -> {s == KL.Install{} : KL.Setup}:
  match f s:
    case KL.Current{} KL.Local{}:
      pk.false_true({KL.Local{} == KL.Install{} : KL.Setup}, fetches)
    case KL.Current{} KL.Install{}:
      {==}
    case KL.Skills{} KL.Local{}:
      pk.false_true({KL.Local{} == KL.Install{} : KL.Setup}, fetches)
    case KL.Skills{} KL.Install{}:
      {==}
    case KL.Stale{} KL.Local{}:
      pk.false_true({KL.Local{} == KL.Install{} : KL.Setup}, fetches)
    case KL.Stale{} KL.Install{}:
      {==}

def pk.fetch_verified_before_use(f: KL.Found, s: KL.Setup) -> {KL.acts.verified(KL.plan(f, s), True{}) == True{} : Bool}:
  match f s:
    case KL.Current{} KL.Local{}:
      {==}
    case KL.Current{} KL.Install{}:
      {==}
    case KL.Skills{} KL.Local{}:
      {==}
    case KL.Skills{} KL.Install{}:
      {==}
    case KL.Stale{} KL.Local{}:
      {==}
    case KL.Stale{} KL.Install{}:
      {==}

def pk.setup_runs(f: KL.Found, s: KL.Setup) -> {KL.acts.runs(KL.plan(f, s)) == True{} : Bool}:
  match f s:
    case KL.Current{} KL.Local{}:
      {==}
    case KL.Current{} KL.Install{}:
      {==}
    case KL.Skills{} KL.Local{}:
      {==}
    case KL.Skills{} KL.Install{}:
      {==}
    case KL.Stale{} KL.Local{}:
      {==}
    case KL.Stale{} KL.Install{}:
      {==}

# The session's tools
# -------------------

def pk.missing_spares_tools(n: Nat, f: KL.Found, ok: Bool) -> {KL.answer(KL.Other{n}, KL.start(f, ok)) == KL.Ran{} : KL.Answer}:
  {==}

def pk.missing_names_install(f: KL.Found, failed: {KL.start(f, False{}) == KL.Missing{} : KL.Kernel}) -> {KL.answer(KL.Python{}, KL.start(f, False{})) == KL.NamesInstall{} : KL.Answer}:
  match f:
    case KL.Current{}:
      pk.up_missing({KL.answer(KL.Python{}, KL.Up{}) == KL.NamesInstall{} : KL.Answer}, failed)
    case KL.Skills{}:
      {==}
    case KL.Stale{}:
      {==}

# The bootstrap lock
# ------------------

def pk.attempt_leaves_none(l: KL.Lock) -> {KL.own_left(KL.attempt(l)) == 0n : Nat}:
  match l:
    case KL.Free{}:
      {==}
    case KL.Live{}:
      {==}
    case KL.Gone{}:
      {==}

def pk.sweep_removes_dead(ls: List<&2, KL.Left>) -> {KL.lefts.dead(KL.sweep(ls)) == 0n : Nat}:
  match ls:
    case Nil{}:
      {==}
    case KL.Left{k, o} <> rest:
      match k o:
        case KL.Cand{} KL.Alive{}:
          pk.sweep_removes_dead(rest)
        case KL.Cand{} KL.Dead{}:
          pk.sweep_removes_dead(rest)
        case KL.Aside{} KL.Alive{}:
          pk.sweep_removes_dead(rest)
        case KL.Aside{} KL.Dead{}:
          pk.sweep_removes_dead(rest)
        case KL.Foreign{} KL.Alive{}:
          pk.sweep_removes_dead(rest)
        case KL.Foreign{} KL.Dead{}:
          pk.sweep_removes_dead(rest)

def pk.sweep_keeps_live(ls: List<&2, KL.Left>) -> {KL.lefts.live(KL.sweep(ls)) == KL.lefts.live(ls) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case KL.Left{k, o} <> rest:
      match k o:
        case KL.Cand{} KL.Alive{}:
          %pk.sweep_keeps_live(rest) : {1n+KL.lefts.live(KL.sweep(rest)) == 1n+_ : Nat}
          {==}
        case KL.Cand{} KL.Dead{}:
          pk.sweep_keeps_live(rest)
        case KL.Aside{} KL.Alive{}:
          %pk.sweep_keeps_live(rest) : {1n+KL.lefts.live(KL.sweep(rest)) == 1n+_ : Nat}
          {==}
        case KL.Aside{} KL.Dead{}:
          pk.sweep_keeps_live(rest)
        case KL.Foreign{} KL.Alive{}:
          %pk.sweep_keeps_live(rest) : {1n+KL.lefts.live(KL.sweep(rest)) == 1n+_ : Nat}
          {==}
        case KL.Foreign{} KL.Dead{}:
          %pk.sweep_keeps_live(rest) : {1n+KL.lefts.live(KL.sweep(rest)) == 1n+_ : Nat}
          {==}

# eukhe: the proof of LAW kernel_ffi_answers
# A plan and every lock but one aged lock are closed strings: they compute.
# An aged lock and a sweep carry a number of the request: the wire's
# round trip reads it back (LWire.pw6.nat), the files read back one by one
# (LKL.kl.lefts_rt), and the reply writers write what the laws spell.

import Base
import ../../bend/ffi_kernel_local.bend as FKL
import ../../bend/kernel_local.bend as KL
import ../../bend/wire.bend as Wr
import ../../laws/kernel_local.bend as KernelLocal
import ../base/wire.bend as LWire
import ./base.bend as LKL

def ka.plan(f: KL.Found, s: KL.Setup) -> {FKL.ffi(KernelLocal.spell_ask(KL.AskPlan{f, s})) == KernelLocal.spell_answer(KL.AskPlan{f, s}) : String}:
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

def ka.lock(x: KL.Seen, fits: {KernelLocal.ask_fits(KL.AskLock{x}) == True{} : Bool}) -> {FKL.ffi(KernelLocal.spell_ask(KL.AskLock{x})) == KernelLocal.spell_answer(KL.AskLock{x}) : String}:
  match x:
    case KL.Linked{}:
      {==}
    case KL.Vanished{}:
      {==}
    case KL.Owner{alive}:
      match alive:
        case True{}:
          {==}
        case False{}:
          {==}
    case KL.NoOwner{age}:
      match age:
        case None{}:
          {==}
        case Some{+n}:
          %LWire.pw6.nat(n, "", fits) : {FKL.run(FKL.get_lock(FKL.get_age.some(_))) == KernelLocal.spell_answer(KL.AskLock{KL.NoOwner{Some{n}}}) : String}
          LKL.kl.lock_old(Nat.is_lt(30000n, n))

def ka.sweep(ls: List<&2, KL.Left>, fits: {KernelLocal.ask_fits(KL.AskSweep{ls}) == True{} : Bool}) -> {FKL.ffi(KernelLocal.spell_ask(KL.AskSweep{ls})) == KernelLocal.spell_answer(KL.AskSweep{ls}) : String}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      %LWire.pw6.nat(1n+List.length(&2, KL.Left, t), KernelLocal.spell_left(l, KernelLocal.spell_lefts(t, "")), fits) : {FKL.run(FKL.get_sweep(_)) == KernelLocal.spell_answer(KL.AskSweep{l <> t}) : String}
      %LKL.kl.lefts_rt(t, l, "") : {FKL.run(FKL.get_sweep.files(_)) == KernelLocal.spell_answer(KL.AskSweep{l <> t}) : String}
      %LKL.kl.keeps_items(l <> t, "") : {Wr.put_nat(List.length(&2, Bool, KL.keeps(l <> t)), _) == Wr.put_nat(List.length(&2, KL.Left, l <> t), KernelLocal.spell_keeps(l <> t, "")) : String}
      %LKL.kl.len_keeps(l <> t) : {Wr.put_nat(_, KernelLocal.spell_keeps(l <> t, "")) == Wr.put_nat(List.length(&2, KL.Left, l <> t), KernelLocal.spell_keeps(l <> t, "")) : String}
      {==}

def KernelLocal.kernel_ffi_answers(a, fits):
  match a:
    case KL.AskPlan{f, s}:
      ka.plan(f, s)
    case KL.AskSweep{ls}:
      ka.sweep(ls, fits)
    case KL.AskLock{x}:
      ka.lock(x, fits)

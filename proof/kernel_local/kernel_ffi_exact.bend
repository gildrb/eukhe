# eukhe: the proof of LAW kernel_ffi_exact
# The entry reads every input as the laws' reader does (LKL.kl.ask); a
# whole request gets the entry's answer, which is the laws' on every
# request (kfe.answer: the plans compute, the sweep's verdicts by
# LKL.kl.keeps_items and LKL.kl.len_keeps, the attempt's end by
# kernel_lock_judge); anything else gets the error form.

import Base
import ../../bend/ffi_kernel_local.bend as FKL
import ../../bend/kernel_local.bend as KL
import ../../bend/wire.bend as Wr
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL
import ./kernel_lock_judge.bend as PKernelLockJudge

def kfe.end_tag(e: KL.End) -> {FKL.put_end(e, "") == KernelLocal.spell_end(e, "") : String}:
  match e:
    case KL.Got{}:
      {==}
    case KL.Busy{}:
      {==}
    case KL.Freed{}:
      {==}
    case KL.Crash{}:
      {==}

def kfe.answer(a: KL.Ask) -> {FKL.answer(a) == KernelLocal.spell_answer(a) : String}:
  match a:
    case KL.AskPlan{f, s}:
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
    case KL.AskSweep{+ls}:
      %LKL.kl.keeps_items(ls, "") : {Wr.put_nat(List.length(&2, Bool, KL.keeps(ls)), _) == Wr.put_nat(List.length(&2, KL.Left, ls), KernelLocal.spell_keeps(ls, "")) : String}
      %LKL.kl.len_keeps(ls) : {Wr.put_nat(_, KernelLocal.spell_keeps(ls, "")) == Wr.put_nat(List.length(&2, KL.Left, ls), KernelLocal.spell_keeps(ls, "")) : String}
      {==}
    case KL.AskLock{+x}:
      %KernelLocal.kernel_lock_judge(x) : {FKL.put_end(KL.attempt(KL.lock.of(x)), "") == KernelLocal.spell_end(_, "") : String}
      kfe.end_tag(KL.attempt(KL.lock.of(x)))

def kfe.fin(b: Bool, a: KL.Ask) -> {FKL.run.end(b, a) == KernelLocal.ffi_spec.read(KernelLocal.read_ask.end(b, a)) : String}:
  match b:
    case True{}:
      kfe.answer(a)
    case False{}:
      {==}

def kfe.whole(r: Wr.Dec<KL.Ask>) -> {FKL.run(r) == KernelLocal.ffi_spec.read(KernelLocal.read_ask.whole(r)) : String}:
  match r:
    case Wr.Got{a, s}:
      kfe.fin(Wr.end(s), a)
    case Wr.Bad{}:
      {==}

def KernelLocal.kernel_ffi_exact(s):
  %LKL.kl.ask(Wr.get_nat(s)) : {FKL.run(_) == KernelLocal.ffi_spec(s) : String}
  kfe.whole(KernelLocal.read_ask.go(Wr.get_nat(s)))

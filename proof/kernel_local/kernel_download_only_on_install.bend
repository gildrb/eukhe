# eukhe: the proof of LAW kernel_download_only_on_install

import Base
import ../../bend/kernel_local.bend as KL
import ../../LAWS.bend as Laws

def pk.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pk.false_true(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pk.BD(_, A, Unit)
  Unit{}

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

def Laws.kernel_download_only_on_install(f, s, fetches):
  pk.download_only_on_install(f, s, fetches)

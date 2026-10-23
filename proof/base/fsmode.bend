# eukhe: lemmas the proofs of two or more areas share: fsmode

import Base
import ../../bend/fsmode.bend as Fs
import ./nat/misc.bend as LNatMisc

def pf.OD(v: Fs.Open, A: Type) -> Type:
  match v:
    case Fs.Opened{p}:
      A
    case Fs.NeedsCwd{}:
      Unit
    case Fs.Gone{p}:
      Unit
    case Fs.NotDir{p}:
      Unit

def pf.needs_opened(-A: Type, +p: Nat, e: {Fs.NeedsCwd{} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

def pf.gone_opened(-A: Type, +q: Nat, +p: Nat, e: {Fs.Gone{q} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

def pf.notdir_opened(-A: Type, +q: Nat, +p: Nat, e: {Fs.NotDir{q} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

def explicit(c: Fs.Cwd, +p: Nat, ok: {Fs.open(c) == Fs.Opened{p} : Fs.Open}) -> {c == Fs.DirCwd{p} : Fs.Cwd}:
  match c:
    case Fs.NoCwd{}:
      pf.needs_opened({Fs.NoCwd{} == Fs.DirCwd{p} : Fs.Cwd}, p, ok)
    case Fs.GoneCwd{q}:
      pf.gone_opened({Fs.GoneCwd{q} == Fs.DirCwd{p} : Fs.Cwd}, q, p, ok)
    case Fs.FileCwd{q}:
      pf.notdir_opened({Fs.FileCwd{q} == Fs.DirCwd{p} : Fs.Cwd}, q, p, ok)
    case Fs.DirCwd{q}:
      Equal.cong(Nat, Fs.Cwd, n => Fs.DirCwd{n}, q, p, Equal.cong(Fs.Open, Nat, LNatMisc.pf.opened_p, Fs.Opened{q}, Fs.Opened{p}, ok))

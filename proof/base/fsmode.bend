# eukhe: lemmas the proofs of two or more areas share: fsmode

import Base
import ../../bend/fsmode.bend as Fs
import ./logic/logic.bend as LLogicLogic
import ./logic/nat.bend as LLogicNat

def explicit(c: Fs.Cwd, +p: Nat, ok: {Fs.open(c) == Fs.Opened{p} : Fs.Open}) -> {c == Fs.DirCwd{p} : Fs.Cwd}:
  match c:
    case Fs.NoCwd{}:
      LLogicLogic.pf.needs_opened({Fs.NoCwd{} == Fs.DirCwd{p} : Fs.Cwd}, p, ok)
    case Fs.GoneCwd{q}:
      LLogicLogic.pf.gone_opened({Fs.GoneCwd{q} == Fs.DirCwd{p} : Fs.Cwd}, q, p, ok)
    case Fs.FileCwd{q}:
      LLogicLogic.pf.notdir_opened({Fs.FileCwd{q} == Fs.DirCwd{p} : Fs.Cwd}, q, p, ok)
    case Fs.DirCwd{q}:
      Equal.cong(Nat, Fs.Cwd, n => Fs.DirCwd{n}, q, p, Equal.cong(Fs.Open, Nat, LLogicNat.pf.opened_p, Fs.Opened{q}, Fs.Opened{p}, ok))

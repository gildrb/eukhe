# eukhe: the proof of LAW orphan_work_exit_due

import Base
import ../../laws/orphan.bend as Orphan
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat

# with n <= p: p <= m - n exactly when n + p <= m (m - n saturates at 0)
def ps.or_le_sub_zero(np: Nat, p: Nat, h: {Nat.is_le(1n+np, p) == True{} : Bool}) -> {Nat.is_le(p, 0n) == Nat.is_le(Nat.add(1n+np, p), 0n) : Bool}:
  match p:
    case 0n:
      LLogicLogic.screen.ps.absurdF({Nat.is_le(0n, 0n) == Nat.is_le(Nat.add(1n+np, 0n), 0n) : Bool}, h)
    case 1n+pp:
      {==}

def ps.or_le_sub(n: Nat, +p: Nat, m: Nat, h: {Nat.is_le(n, p) == True{} : Bool}) -> {Nat.is_le(p, Nat.sub(m, n)) == Nat.is_le(Nat.add(n, p), m) : Bool}:
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+mp:
      {==}
    case 1n+(+np) 0n:
      ps.or_le_sub_zero(np, p, h)
    case 1n+(+np) 1n+mp:
      ps.or_le_sub(np, p, mp, LNat.screen.ps.le_trans(np, 1n+np, p, LNat.screen.ps.le_succ(np), h))

def Orphan.orphan_work_exit_due(window, absent):
  ps.or_le_sub(window, window, absent, LNat.screen.ps.le_refl(window))

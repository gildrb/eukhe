# eukhe: the proof of LAW stall_retry_doubles
# (1 + t) + (1 + t) is 2 + (t + t) (add_succ), and (t + t) + 2 is
# 2 + (t + t) (rd.plus_two).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/nat.bend as LNat

# x + 2 is 2 + x
def rd.plus_two(x: Nat) -> {Nat.add(x, 2n) == 2n+x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.add(p, 2n), 2n+p, rd.plus_two(p))

def doubles(+t: Nat) -> {R.stall.next(0n) == 0n : Nat} & {R.stall.next(1n+t) == Nat.add(R.stall.next(t), 2n) : Nat}:
  +tt = Nat.add(t, t)
  +step = Equal.cong(Nat, Nat, y => 1n+y, Nat.add(t, 1n+t), 1n+tt, LNat.add_succ(t, t))
  ({==}, Equal.trans(Nat, 1n+Nat.add(t, 1n+t), 2n+tt, Nat.add(tt, 2n), step, Equal.sym(Nat, Nat.add(tt, 2n), 2n+tt, rd.plus_two(tt))))

def Retry.stall_retry_doubles(t):
  doubles(t)

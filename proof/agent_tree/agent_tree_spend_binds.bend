# eukhe: the proof of LAW agent_tree_spend_binds
#
# PROOF: with L = a + (c + k): the root's room is L - 0 = L and a <= L,
# so the spend of a is taken (spend 0 + a = a); the room is then
# L - a = c + k and c <= c + k, so the spend of c is taken (spend a + c);
# the room is then L - (a + c) = k, and k + 1 <= k is False: NoBudget

import Base
import ../../bend/agent_tree.bend as T
import ../../laws/agent_tree.bend as AgentTree

def sb.sub0(+x: Nat) -> {x == Nat.sub(x, 0n) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sb.sub_add(+a: Nat, +k: Nat) -> {k == Nat.sub(Nat.add(a, k), a) : Nat}:
  match a:
    case 0n:
      sb.sub0(k)
    case 1n+p:
      sb.sub_add(p, k)

def sb.sub_add2(+a: Nat, +c: Nat, +k: Nat) -> {k == Nat.sub(Nat.add(a, Nat.add(c, k)), Nat.add(a, c)) : Nat}:
  match a:
    case 0n:
      sb.sub_add(c, k)
    case 1n+p:
      sb.sub_add2(p, c, k)

def sb.le0(+k: Nat) -> {True{} == Nat.is_le(0n, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sb.le_add(+a: Nat, +k: Nat) -> {True{} == Nat.is_le(a, Nat.add(a, k)) : Bool}:
  match a:
    case 0n:
      sb.le0(k)
    case 1n+p:
      sb.le_add(p, k)

def sb.lt(+k: Nat) -> {False{} == Nat.is_le(1n+k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      sb.lt(p)

def AgentTree.agent_tree_spend_binds(b, s, a, c, k, dl):
  %sb.sub0(Nat.add(a, Nat.add(c, k))) : {[T.spend_fits(Nat.is_le(a, _), T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, 0n, dl, []}}, a), T.step(b, T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}, T.EvSpend{[], c}), T.step(b, T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}, T.EvSpend{[], 1n+k})] == [T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}}, T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}}, T.Refused{T.NoBudget{}}] : List<&2, T.Step>}
  %sb.le_add(a, Nat.add(c, k)) : {[T.spend_fits(_, T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, 0n, dl, []}}, a), T.step(b, T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}, T.EvSpend{[], c}), T.step(b, T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}, T.EvSpend{[], 1n+k})] == [T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}}, T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}}, T.Refused{T.NoBudget{}}] : List<&2, T.Step>}
  %sb.sub_add(a, Nat.add(c, k)) : {[T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}}, T.spend_fits(Nat.is_le(c, _), T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}, c), T.step(b, T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}, T.EvSpend{[], 1n+k})] == [T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}}, T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}}, T.Refused{T.NoBudget{}}] : List<&2, T.Step>}
  %sb.le_add(c, k) : {[T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}}, T.spend_fits(_, T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}, c), T.step(b, T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}, T.EvSpend{[], 1n+k})] == [T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}}, T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}}, T.Refused{T.NoBudget{}}] : List<&2, T.Step>}
  %sb.sub_add2(a, c, k) : {[T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}}, T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}}, T.spend_fits(Nat.is_le(1n+k, _), T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}, 1n+k)] == [T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}}, T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}}, T.Refused{T.NoBudget{}}] : List<&2, T.Step>}
  %sb.lt(k) : {[T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}}, T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}}, T.spend_fits(_, T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}, 1n+k)] == [T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, a, dl, []}}}, T.Took{T.Leaf{T.Info{T.Running{}, s, T.Value{Nat.add(a, Nat.add(c, k))}, Nat.add(a, c), dl, []}}}, T.Refused{T.NoBudget{}}] : List<&2, T.Step>}
  {==}

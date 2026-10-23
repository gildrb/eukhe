# eukhe: the proof of LAW peer_same_uid

import Base
import ../../bend/fsmode.bend as Fs
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pf.PD(v: Fs.Peer, A: Type) -> Type:
  match v:
    case Fs.Accept{}:
      A
    case Fs.Drop{}:
      Unit

def pf.drop_accept(-A: Type, e: {Fs.Drop{} == Fs.Accept{} : Fs.Peer}) -> A:
  %e : pf.PD(_, A)
  Unit{}

def pf.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LA.fsmode.pf.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LA.fsmode.pf.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pf.eq_true(p, q, h))

# Socket peers
# ------------

def pf.peer_at(b: Bool, +p: Nat, +own: Nat, eb: {Nat.is_eq(p, own) == b : Bool}, ok: {Fs.peer.at(b) == Fs.Accept{} : Fs.Peer}) -> {p == own : Nat}:
  match b:
    case True{}:
      pf.eq_true(p, own, eb)
    case False{}:
      pf.drop_accept({p == own : Nat}, ok)

def peer_same(+p: Nat, +own: Nat, ok: {Fs.peer(p, own) == Fs.Accept{} : Fs.Peer}) -> {p == own : Nat}:
  pf.peer_at(Nat.is_eq(p, own), p, own, {==}, ok)

def Laws.peer_same_uid(p, own, ok):
  peer_same(p, own, ok)

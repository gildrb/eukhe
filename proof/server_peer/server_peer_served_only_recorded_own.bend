# eukhe: the proof of LAW server_peer_served_only_recorded_own
#
# PROOF: case by case on the decisions: another uid answers OtherUid, no
# record NoRecord, another pid OtherPid; so Served means the uid is the
# client's (spb.eq_true), a record above 0, and the pid equal to it.

import Base
import ../../bend/server_peer.bend as Sp
import ../../laws/server_peer.bend as ServerPeer
import ./base.bend as LA

def spo.pid(b: Bool, +pid: Nat, +r: Nat, eb: {Nat.is_eq(pid, r) == b : Bool}, ok: {Sp.served.pid(b) == Sp.Served{} : Sp.Served}) -> {pid == r : Nat}:
  match b:
    case True{}:
      LA.spb.eq_true(pid, r, eb)
    case False{}:
      LA.spb.pid_served({pid == r : Nat}, ok)

def spo.rec(+pid: Nat, rec: Nat, ok: {Sp.served.rec(pid, rec) == Sp.Served{} : Sp.Served}) -> {pid == rec : Nat} & {Nat.is_eq(rec, 0n) == False{} : Bool}:
  match rec:
    case 0n:
      LA.spb.none_served({pid == 0n : Nat} & {Nat.is_eq(0n, 0n) == False{} : Bool}, ok)
    case 1n+q:
      +r : Nat = 1n+q
      (spo.pid(Nat.is_eq(pid, r), pid, r, {==}, ok), {==})

def spo.uid(b: Bool, +p: Nat, +own: Nat, +pid: Nat, rec: Nat, eb: {Nat.is_eq(p, own) == b : Bool}, ok: {Sp.served.uid(b, pid, rec) == Sp.Served{} : Sp.Served}) -> {p == own : Nat} & ({pid == rec : Nat} & {Nat.is_eq(rec, 0n) == False{} : Bool}):
  match b:
    case True{}:
      (LA.spb.eq_true(p, own, eb), spo.rec(pid, rec, ok))
    case False{}:
      LA.spb.uid_served({p == own : Nat} & ({pid == rec : Nat} & {Nat.is_eq(rec, 0n) == False{} : Bool}), ok)

def ServerPeer.server_peer_served_only_recorded_own(p, own, pid, rec, ok):
  spo.uid(Nat.is_eq(p, own), p, own, pid, rec, {==}, ok)

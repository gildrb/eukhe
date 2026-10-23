# eukhe: the proof of LAW peer_own_accepted

import Base
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode

# Numbers
# -------

def pf.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pf.eq_refl(p)

def peer_own(+own: Nat) -> {Fs.peer(own, own) == Fs.Accept{} : Fs.Peer}:
  %pf.eq_refl(own) : {Fs.peer.at(_) == Fs.Accept{} : Fs.Peer}
  {==}

def Fsmode.peer_own_accepted(own):
  peer_own(own)

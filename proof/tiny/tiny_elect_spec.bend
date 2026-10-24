# eukhe: the proof of LAW tiny_elect_spec
#
# PROOF: a case per probe; on a pong the code's comparison is the spec's
# (LA.te.same), and both pick Join on True and Replace on False.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/base.bend as LawsBase
import ../../laws/tiny.bend as Tiny
import ./base.bend as LA

def te.elect_pong(b: Bool) -> {Tn.elect.pong(b) == Tiny.sp_pong(b, Tn.Join{}, Tn.Replace{}) : Tn.Act}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Tiny.tiny_elect_spec(p, m):
  match p:
    case Tn.Missing{}:
      {==}
    case Tn.Unreachable{}:
      {==}
    case Tn.Pong{+t}:
      %LA.te.same(t, m) : {Tn.elect.pong(Tn.same(t, m)) == Tiny.sp_pong(_, Tn.Join{}, Tn.Replace{}) : Tn.Act}
      te.elect_pong(Tn.same(t, m))
    case Tn.Odd{}:
      {==}
    case Tn.Garbled{}:
      {==}
    case Tn.Hung{}:
      {==}

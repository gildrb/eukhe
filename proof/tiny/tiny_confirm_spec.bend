# eukhe: the proof of LAW tiny_confirm_spec
#
# PROOF: a case per probe; on a pong the code's comparison is the spec's
# (LA.te.same), and both pick Serving on True and Mistagged on False.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/elect.bend as Tiny
import ./base.bend as LA

def te.confirm_pong(b: Bool) -> {Tn.confirm.pong(b) == Tiny.sp_check(b) : Tn.Check}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Tiny.tiny_confirm_spec(p, m):
  match p:
    case Tn.Missing{}:
      {==}
    case Tn.Unreachable{}:
      {==}
    case Tn.Pong{+t}:
      %LA.te.same(t, m) : {Tn.confirm.pong(Tn.same(t, m)) == Tiny.sp_check(_) : Tn.Check}
      te.confirm_pong(Tn.same(t, m))
    case Tn.Odd{}:
      {==}
    case Tn.Garbled{}:
      {==}
    case Tn.Hung{}:
      {==}

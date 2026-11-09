# eukhe: the proof of LAW proto_all_ok_each
#
# PROOF: by induction on the frames before f: all_ok is an and of each
# frame's acceptance, so a true one is true at f (left side) after the
# frames before it (right sides).

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA
import ../base/logic/bool.bend as LLogicBool

def pae.go(pre: List<&2, Sb.Frame>, +f: Sb.Frame, +post: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>, h: {Sb.all_ok(List.append(&2, Sb.Frame, pre, f <> post), max, allowed) == True{} : Bool}) -> {Sb.accepts(max, allowed, f) == True{} : Bool}:
  match pre:
    case Nil{}:
      LLogicBool.wr_and_l(Sb.accepts(max, allowed, f), Sb.all_ok(post, max, allowed), h)
    case +g <> +rest:
      pae.go(rest, f, post, max, allowed, LLogicBool.wr_and_r(Sb.accepts(max, allowed, g), Sb.all_ok(List.append(&2, Sb.Frame, rest, f <> post), max, allowed), h))

def Sandbox.proto_all_ok_each(pre, f, post, max, allowed, h):
  pae.go(pre, f, post, max, allowed, h)

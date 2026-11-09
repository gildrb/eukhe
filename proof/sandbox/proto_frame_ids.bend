# eukhe: the proof of LAW proto_frame_ids
#
# PROOF: by induction on the first list: each frame's id goes in front of
# the ids of the rest joined (pfi.go); one frame's ids are its id, by
# evaluation.

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

def pfi.go(a: List<&2, Sb.Frame>, +b: List<&2, Sb.Frame>) -> {Sb.frame.ids(List.append(&2, Sb.Frame, a, b)) == List.append(&2, Nat, Sb.frame.ids(a), Sb.frame.ids(b)) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case +f <> +rest:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Sb.Frame.id(f) <> z, Sb.frame.ids(List.append(&2, Sb.Frame, rest, b)), List.append(&2, Nat, Sb.frame.ids(rest), Sb.frame.ids(b)), pfi.go(rest, b))

def Sandbox.proto_frame_ids(a, b, i, l, k):
  (pfi.go(a, b), {==})

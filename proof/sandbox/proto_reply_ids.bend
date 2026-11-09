# eukhe: the proof of LAW proto_reply_ids
#
# PROOF: by induction on the first list: each reply's id goes in front of
# the ids of the rest joined (pri.go); one reply's ids are its id, by
# evaluation.

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

def pri.go(a: List<&2, Sb.Reply>, +b: List<&2, Sb.Reply>) -> {Sb.reply.ids(List.append(&2, Sb.Reply, a, b)) == List.append(&2, Nat, Sb.reply.ids(a), Sb.reply.ids(b)) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case +r <> +rest:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Sb.Reply.id(r) <> z, Sb.reply.ids(List.append(&2, Sb.Reply, rest, b)), List.append(&2, Nat, Sb.reply.ids(rest), Sb.reply.ids(b)), pri.go(rest, b))

def Sandbox.proto_reply_ids(a, b, i):
  (pri.go(a, b), ({==}, {==}))

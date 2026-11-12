# eukhe: the proof of LAW thread_log_append
#
# PROOF: by induction on the first stream: its first message is kept or
# skipped in front of the rest's log either way (tla.keep, by cases on
# whether the session wrote it).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./base.bend as LA

def tla.keep(b: Bool, m: Th.Msg, x: List<&2, Th.Msg>, +y: List<&2, Th.Msg>) -> {Th.log.keep(b, m, List.append(&2, Th.Msg, x, y)) == List.append(&2, Th.Msg, Th.log.keep(b, m, x), y) : List<&2, Th.Msg>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tla.go(+s: Nat, a: List<&2, Th.Msg>, +b: List<&2, Th.Msg>) -> {Th.log(s, List.append(&2, Th.Msg, a, b)) == List.append(&2, Th.Msg, Th.log(s, a), Th.log(s, b)) : List<&2, Th.Msg>}:
  match a:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case Th.Msg{+who, +body}:
          %Equal.sym(List<&2, Th.Msg>, Th.log(s, List.append(&2, Th.Msg, t, b)), List.append(&2, Th.Msg, Th.log(s, t), Th.log(s, b)), tla.go(s, t, b)) : {Th.log.keep(Nat.is_eq(who, s), Th.Msg{who, body}, _) == List.append(&2, Th.Msg, Th.log.keep(Nat.is_eq(who, s), Th.Msg{who, body}, Th.log(s, t)), Th.log(s, b)) : List<&2, Th.Msg>}
          tla.keep(Nat.is_eq(who, s), Th.Msg{who, body}, Th.log(s, t), Th.log(s, b))

def Thread.thread_log_append(s, a, b):
  tla.go(s, a, b)

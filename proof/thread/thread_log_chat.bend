# eukhe: the proof of LAW thread_log_chat
#
# PROOF: by induction on the stream: a message the session wrote is kept
# in front of the rest's chat, any other is skipped; the spec's chat
# appends the same one-message (or empty) list (tlc.keep, by cases on
# whether the session wrote it).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread

def tlc.keep(b: Bool, m: Th.Msg, rest: List<&2, Th.Msg>) -> {Th.log.keep(b, m, rest) == List.append(&2, Th.Msg, S.only(b, m), rest) : List<&2, Th.Msg>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tlc.go(+s: Nat, evs: List<&2, Th.Msg>) -> {Th.log(s, evs) == S.chat(s, evs) : List<&2, Th.Msg>}:
  match evs:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case Th.Msg{+who, +body}:
          %tlc.go(s, t) : {Th.log.keep(Nat.is_eq(who, s), Th.Msg{who, body}, Th.log(s, t)) == List.append(&2, Th.Msg, S.only(Nat.is_eq(who, s), Th.Msg{who, body}), _) : List<&2, Th.Msg>}
          tlc.keep(Nat.is_eq(who, s), Th.Msg{who, body}, Th.log(s, t))

def Thread.thread_log_chat(s, evs):
  tlc.go(s, evs)

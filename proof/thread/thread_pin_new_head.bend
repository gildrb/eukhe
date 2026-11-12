# eukhe: the proof of LAW thread_pin_new_head
#
# PROOF: the pin's head differs from the call's (the premise moved), so
# the call pins the fresh render under its own head: both claims compute
# (thp.keep, by cases on the head comparison).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./base.bend as LA

def thp.keep(b: Bool, +h0: Nat, +v: List<&2, Th.Span>, +h: Nat, +fresh: List<&2, Th.Span>, -s: Nat, -evs: List<&2, Th.Msg>, -w: Nat, e: {b == False{} : Bool}) -> {Th.request(s, evs, Thread.sp_view(Th.pin.keep(b, Th.Pin{h0, v}, h, fresh)), w) == Th.request(s, evs, fresh, w) : List<&2, Th.Item>} & {Thread.sp_head(Th.pin.keep(b, Th.Pin{h0, v}, h, fresh)) == h : Nat}:
  match b:
    case True{}:
      LA.thb.absurd_tf({Th.request(s, evs, Thread.sp_view(Th.Pin{h0, v}), w) == Th.request(s, evs, fresh, w) : List<&2, Th.Item>} & {Thread.sp_head(Th.Pin{h0, v}) == h : Nat}, e)
    case False{}:
      ({==}, {==})

def Thread.thread_pin_new_head(p, h, fresh, s, evs, w, moved):
  match p:
    case Th.Pin{+h0, +v}:
      thp.keep(Nat.is_eq(h0, h), h0, v, h, fresh, s, evs, w, moved)

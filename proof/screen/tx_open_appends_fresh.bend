# eukhe: the proof of LAW tx_open_appends_fresh
#
# PROOF: the Open appends Blk{n, Active, 0} to the blocks; induction on the
# blocks: each pairs with itself, and the last new one is active and empty.

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen/events.bend as ScreenEvents
import ./base/events.bend as LAScreenEvents

def open.blocks(bs: List<&2, Sc.Blk>, +n: Nat) -> {ScreenEvents.tx_fresh_after(bs, List.append(&2, Sc.Blk, bs, [Sc.Blk{n, Sc.Active{}, 0n}])) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +br:
      match b:
        case Sc.Blk{+i, +s, +l}:
          LAScreenEvents.ev.and_t(ScreenEvents.tx_same(Sc.Blk{i, s, l}, Sc.Blk{i, s, l}), ScreenEvents.tx_fresh_after(br, List.append(&2, Sc.Blk, br, [Sc.Blk{n, Sc.Active{}, 0n}])), LAScreenEvents.ev.and3(Nat.is_eq(i, i), ScreenEvents.tx_st_eq(s, s), Nat.is_eq(l, l), LAScreenEvents.ev.t(i), LAScreenEvents.ev.st_t(s), LAScreenEvents.ev.t(l)), open.blocks(br, n))

def open.law(+t: Sc.Tx) -> {ScreenEvents.tx_fresh_after(Sc.Tx.blocks(t), Sc.Tx.blocks(Sc.step(t, Sc.Open{}))) == True{} : Bool}:
  match t:
    case Sc.Tx{bs, n, w}:
      open.blocks(bs, n)

def ScreenEvents.tx_open_appends_fresh(t):
  open.law(t)

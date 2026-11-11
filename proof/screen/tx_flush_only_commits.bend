# eukhe: the proof of LAW tx_flush_only_commits
#
# PROOF: induction on the blocks along the flush: a committed or final block
# heads the result committed, an active one ends the flush and the rest is
# kept, which tx_committed accepts pair by pair (flush.kept).

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen/events.bend as ScreenEvents
import ./base/events.bend as LAScreenEvents

def flush.head(+i: Nat, +l: Nat) -> {Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(l, l), True{})) == True{} : Bool}:
  LAScreenEvents.ev.and3(Nat.is_eq(i, i), Nat.is_eq(l, l), True{}, LAScreenEvents.ev.t(i), LAScreenEvents.ev.t(l), {==})

# blocks kept as they are
def flush.kept(bs: List<&2, Sc.Blk>) -> {ScreenEvents.tx_committed(bs, bs) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +br:
      match b:
        case Sc.Blk{+i, s, +l}:
          match s:
            case Sc.Active{}:
              LAScreenEvents.ev.and_t(Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(l, l), True{})), ScreenEvents.tx_committed(br, br), flush.head(i, l), flush.kept(br))
            case Sc.Final{}:
              LAScreenEvents.ev.and_t(Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(l, l), True{})), ScreenEvents.tx_committed(br, br), flush.head(i, l), flush.kept(br))
            case Sc.Comm{}:
              LAScreenEvents.ev.and_t(Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(l, l), True{})), ScreenEvents.tx_committed(br, br), flush.head(i, l), flush.kept(br))

def flush.blocks(bs: List<&2, Sc.Blk>) -> {ScreenEvents.tx_committed(bs, Sc.flush(bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +br:
      match b:
        case Sc.Blk{+i, s, +l}:
          match s:
            case Sc.Active{}:
              LAScreenEvents.ev.and_t(Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(l, l), True{})), ScreenEvents.tx_committed(br, br), flush.head(i, l), flush.kept(br))
            case Sc.Final{}:
              LAScreenEvents.ev.and_t(Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(l, l), True{})), ScreenEvents.tx_committed(br, Sc.flush(br)), flush.head(i, l), flush.blocks(br))
            case Sc.Comm{}:
              LAScreenEvents.ev.and_t(Bool.and(Nat.is_eq(i, i), Bool.and(Nat.is_eq(l, l), True{})), ScreenEvents.tx_committed(br, Sc.flush(br)), flush.head(i, l), flush.blocks(br))

def flush.law(+t: Sc.Tx) -> {ScreenEvents.tx_committed(Sc.Tx.blocks(t), Sc.Tx.blocks(Sc.step(t, Sc.Flush{}))) == True{} : Bool}:
  match t:
    case Sc.Tx{bs, n, w}:
      flush.blocks(bs)

def ScreenEvents.tx_flush_only_commits(t):
  flush.law(t)

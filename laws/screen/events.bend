# eukhe: the laws of area screen, section events: each event of the transcript
# (bend/screen.bend 1, requirements R1 to R4 of laws/screen/interface.bend), stated
# block by block from the requirement, not from the model's code

import Base
import ../../bend/screen.bend as Sc

# Block by block
# --------------
# Each law relates the blocks before one event (any transcript: any blocks,
# any ids, duplicate ids too, any states and lengths) to the blocks after
# it, pair by pair: a predicate over two lists that fails when their lengths
# differ. Together with tx_flush_settles and tx_gapless
# (laws/screen/interface.bend) they pin every event of a transcript run from
# the empty one.

# the two states are the same
def tx_st_eq(a: Sc.St, b: Sc.St) -> Bool:
  match a b:
    case Sc.Active{} Sc.Active{}:
      True{}
    case Sc.Active{} Sc.Final{}:
      False{}
    case Sc.Active{} Sc.Comm{}:
      False{}
    case Sc.Final{} Sc.Active{}:
      False{}
    case Sc.Final{} Sc.Final{}:
      True{}
    case Sc.Final{} Sc.Comm{}:
      False{}
    case Sc.Comm{} Sc.Active{}:
      False{}
    case Sc.Comm{} Sc.Final{}:
      False{}
    case Sc.Comm{} Sc.Comm{}:
      True{}

def tx_active(s: Sc.St) -> Bool:
  match s:
    case Sc.Active{}:
      True{}
    case Sc.Final{}:
      False{}
    case Sc.Comm{}:
      False{}

def tx_final(s: Sc.St) -> Bool:
  match s:
    case Sc.Active{}:
      False{}
    case Sc.Final{}:
      True{}
    case Sc.Comm{}:
      False{}

def tx_comm(s: Sc.St) -> Bool:
  match s:
    case Sc.Active{}:
      False{}
    case Sc.Final{}:
      False{}
    case Sc.Comm{}:
      True{}

# Open (R1)
# ---------

# the ids of the blocks, in order
def tx_ids(bs: List<&2, Sc.Blk>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      match b:
        case Sc.Blk{i, s, l}:
          i <> tx_ids(rest)

# c ids from n: n, n + 1, ..., n + c - 1
def tx_from(c: Nat, +n: Nat) -> List<&2, Nat>:
  match c:
    case 0n:
      Nil{}
    case 1n+d:
      n <> tx_from(d, 1n+n)

# the Opens among the events
def tx_opens(es: List<&2, Sc.Ev>) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case Sc.Open{}:
          1n+tx_opens(rest)
        case Sc.Grow{x, k}:
          tx_opens(rest)
        case Sc.Fin{x}:
          tx_opens(rest)
        case Sc.Flush{}:
          tx_opens(rest)
        case Sc.Resize{v}:
          tx_opens(rest)

# the ids of a transcript's blocks and its next id
def tx_ids_next(t: Sc.Tx) -> List<&2, Nat> & Nat:
  match t:
    case Sc.Tx{bs, n, w}:
      (tx_ids(bs), n)

# LAW tx_ids_count_opens (R1): after any events on any transcript (blocks
# bs, next id n, any width), the blocks' ids are bs's ids, in order, then
# one new id per Open: n, n + 1, ..., in the order of the Opens; the next
# id is n plus the number of Opens. No event but Open adds, drops, moves or
# renumbers a block, and only Open moves the next id
# EXCLUDES: an Open with another id than the next, or that does not count
#   it up; a block dropped, duplicated or reordered by any event (a flush
#   that drops committed blocks, a grow that moves a block); a next id moved
#   by another event
law tx_ids_count_opens:
  for es: List<&2, Sc.Ev>
  for +bs: List<&2, Sc.Blk>
  for +n: Nat
  for +w: Nat
  {tx_ids_next(Sc.run(es, Sc.Tx{bs, n, w})) == (List.append(&2, Nat, tx_ids(bs), tx_from(tx_opens(es), n)), Nat.add(tx_opens(es), n)) : List<&2, Nat> & Nat}

# the blocks b and c have the same id, state and length
def tx_same(b: Sc.Blk, c: Sc.Blk) -> Bool:
  match b c:
    case Sc.Blk{i, s, l} Sc.Blk{j, t, m}:
      Bool.and(Nat.is_eq(i, j), Bool.and(tx_st_eq(s, t), Nat.is_eq(l, m)))

def tx_none(cs: List<&2, Sc.Blk>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, cr}:
      False{}

# cs is the blocks bs, unchanged, then one more block, active and empty
def tx_fresh_after(bs: List<&2, Sc.Blk>, cs: List<&2, Sc.Blk>) -> Bool:
  match bs cs:
    case Nil{} Nil{}:
      False{}
    case Nil{} Con{c, cr}:
      match c:
        case Sc.Blk{i, s, l}:
          Bool.and(tx_active(s), Bool.and(Nat.is_eq(l, 0n), tx_none(cr)))
    case Con{b, br} Nil{}:
      False{}
    case Con{b, br} Con{c, cr}:
      Bool.and(tx_same(b, c), tx_fresh_after(br, cr))

# LAW tx_open_appends_fresh (R1): on any transcript, an Open keeps every
# block as it was and adds one block after them, active (it still grows)
# and empty (its id is tx_ids_count_opens's)
# EXCLUDES: a new block that starts final or committed (it never grows, or
#   it is flushed empty), with text, or before the others; an Open that
#   changes a block
law tx_open_appends_fresh:
  for +t: Sc.Tx
  {tx_fresh_after(Sc.Tx.blocks(t), Sc.Tx.blocks(Sc.step(t, Sc.Open{}))) == True{} : Bool}

# Grow (R2)
# ---------

# the cap of a block's length: 2^32 - 1 characters (no block holds 4 GiB)
def tx_cap() -> Nat:
  4294967295n

# a length l grown by k under the cap c: l + k when that is at most c; past
# it, c, or l when l is past c already (a length is never cut)
def tx_grown.of(fits: Bool, past: Bool, +l: Nat, k: Nat, c: Nat) -> Nat:
  match fits:
    case True{}:
      Nat.add(l, k)
    case False{}:
      match past:
        case True{}:
          l
        case False{}:
          c

def tx_grown(+l: Nat, +k: Nat) -> Nat:
  tx_grown.of(Nat.is_le(Nat.add(l, k), tx_cap()), Nat.is_lt(tx_cap(), l), l, k, tx_cap())

# the length after the growth: grown when the block grows (hit), else l
def tx_grew.len(hit: Bool, +l: Nat, k: Nat) -> Nat:
  match hit:
    case True{}:
      tx_grown(l, k)
    case False{}:
      l

# block {j, t, m} is block {i, s, l} after a growth of k of the blocks of id
# x (hit: i is x): same id and state; the grown length when it is active
# and hit, else the same length
def tx_grew.at(hit: Bool, +i: Nat, +s: Sc.St, l: Nat, j: Nat, t: Sc.St, m: Nat, k: Nat) -> Bool:
  Bool.and(Nat.is_eq(i, j), Bool.and(tx_st_eq(s, t), Nat.is_eq(m, tx_grew.len(Bool.and(hit, tx_active(s)), l, k))))

def tx_grew.blk(+x: Nat, k: Nat, b: Sc.Blk, c: Sc.Blk) -> Bool:
  match b c:
    case Sc.Blk{+i, s, l} Sc.Blk{j, t, m}:
      tx_grew.at(Nat.is_eq(i, x), i, s, l, j, t, m, k)

# cs is bs after a growth of k of the blocks of id x, pair by pair
def tx_grew(+x: Nat, +k: Nat, bs: List<&2, Sc.Blk>, cs: List<&2, Sc.Blk>) -> Bool:
  match bs cs:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{c, cr}:
      False{}
    case Con{b, br} Nil{}:
      False{}
    case Con{b, br} Con{c, cr}:
      Bool.and(tx_grew.blk(x, k, b, c), tx_grew(x, k, br, cr))

# LAW tx_grow_lengthens (R2): on any transcript, Grow{x, k} lengthens each
# active block of id x by k characters, up to 2^32 - 1 (a length that would
# pass it stops at it; a length already past it stays), and changes nothing
# else: every block keeps its id, its state and its place; a final or
# committed block of id x and every block of another id keep their length
# EXCLUDES: a growth by another amount, lost or doubled; a growth of a final
#   or committed block (fixed text changed); a growth of a block of another
#   id; a cap other than 2^32 - 1, or a cap that cuts a longer block; a
#   growth that changes a state or drops a block
law tx_grow_lengthens:
  for +t: Sc.Tx
  for +x: Nat
  for +k: Nat
  {tx_grew(x, k, Sc.Tx.blocks(t), Sc.Tx.blocks(Sc.step(t, Sc.Grow{x, k}))) == True{} : Bool}

# Fin (R3)
# --------

# block {j, t, m} is block {i, s, l} after the blocks of id x are made final
# (hit: i is x): same id and length; the same state, or final from active
# when hit; and when hit, not active
def tx_finished.at(+hit: Bool, +i: Nat, +s: Sc.St, +l: Nat, j: Nat, +t: Sc.St, m: Nat) -> Bool:
  Bool.and(Nat.is_eq(i, j), Bool.and(Nat.is_eq(l, m), Bool.and(Bool.or(tx_st_eq(s, t), Bool.and(hit, Bool.and(tx_active(s), tx_final(t)))), Bool.or(Bool.not(hit), Bool.not(tx_active(t))))))

def tx_finished.blk(+x: Nat, b: Sc.Blk, c: Sc.Blk) -> Bool:
  match b c:
    case Sc.Blk{+i, s, l} Sc.Blk{j, t, m}:
      tx_finished.at(Nat.is_eq(i, x), i, s, l, j, t, m)

# cs is bs after the blocks of id x are made final, pair by pair
def tx_finished(+x: Nat, bs: List<&2, Sc.Blk>, cs: List<&2, Sc.Blk>) -> Bool:
  match bs cs:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{c, cr}:
      False{}
    case Con{b, br} Nil{}:
      False{}
    case Con{b, br} Con{c, cr}:
      Bool.and(tx_finished.blk(x, b, c), tx_finished(x, br, cr))

# LAW tx_fin_finishes (R3): on any transcript, Fin{x} leaves no block of id
# x active: each active one becomes final; a final or committed block of id
# x keeps its state, and so does every block of another id; ids, lengths and
# places never change
# EXCLUDES: a Fin that leaves its block active (it is never flushed), that
#   commits it at once or makes a committed block final again, that
#   finishes a block of another id, or that changes a length or drops a
#   block
law tx_fin_finishes:
  for +t: Sc.Tx
  for +x: Nat
  {tx_finished(x, Sc.Tx.blocks(t), Sc.Tx.blocks(Sc.step(t, Sc.Fin{x}))) == True{} : Bool}

# Flush (R4)
# ----------

# block {j, t, m} is block {i, s, l}, or that block committed from final:
# same id and length; the same state, or committed from final
def tx_committed.blk(b: Sc.Blk, c: Sc.Blk) -> Bool:
  match b c:
    case Sc.Blk{i, +s, l} Sc.Blk{j, +t, m}:
      Bool.and(Nat.is_eq(i, j), Bool.and(Nat.is_eq(l, m), Bool.or(tx_st_eq(s, t), Bool.and(tx_final(s), tx_comm(t)))))

# cs is bs with some final blocks committed, pair by pair
def tx_committed(bs: List<&2, Sc.Blk>, cs: List<&2, Sc.Blk>) -> Bool:
  match bs cs:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{c, cr}:
      False{}
    case Con{b, br} Nil{}:
      False{}
    case Con{b, br} Con{c, cr}:
      Bool.and(tx_committed.blk(b, c), tx_committed(br, cr))

# LAW tx_flush_only_commits (R4): on any transcript, a flush changes no
# block but to commit a final one: every block keeps its id, its length and
# its place, and its state unless it was final and is now committed. With
# tx_flush_settles (no final block before the first one not committed) and
# tx_gapless (no committed block after one not committed), on every
# transcript run from the empty one this pins the flush: the final blocks
# before the first active one are committed, nothing else
# EXCLUDES: a flush that commits an active block (text still growing
#   written to the scrollback), drops, reorders or shortens a block, or
#   makes a block active or final again
law tx_flush_only_commits:
  for +t: Sc.Tx
  {tx_committed(Sc.Tx.blocks(t), Sc.Tx.blocks(Sc.step(t, Sc.Flush{}))) == True{} : Bool}

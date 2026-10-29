import Mathlib

/-!
# eukhe: the OptChat memory — the pure core of the chat's memory

This file is the Lean 4 formalization of eukhe's chat memory, the pure core
after Victor Taelin's OptChat gist. It is the Lean counterpart of the Bend
model in `bend/optchat/` and the laws in `laws/optchat.bend` of
`gildrb/eukhe`.

The model, in three parts (as `bendtt.lean`):

1. THEORY: binary numbers (lowest bit first), the tree nodes and their
   geometry, the built nodes (tries), the chat's state and events, the
   reference batch (the due measure, the most due mergeable pair, merging
   until the view fits), Taelin's rollback push, the reference step, a
   compaction's view, and the work queue.
2. CLAIMS: the laws — the view and the compaction view tile the messages;
   a message appends its line and merges nothing when no batch runs; a merge
   replaces one sibling pair by its built parent and keeps the coverage; a
   fit ends at its budget unless no pair can merge and merges only into built
   parents; after any history every merged line is built; the due order
   (T - last) / 2^l makes exactly the merges of Taelin's rollback push; a
   compaction's view ends at its node and is a prefix of the compaction view;
   and the queue never stalls a waiting turn.
3. PROOF: the lemmas, in order.

A node(l, i) covers the 2^l messages from i·2^l on (gist §2). Its index i is
kept in binary, lowest bit first, so its parent is one step away: node(l+1,
i/2) drops the lowest bit. The view is an ordered list of nodes (gist §3).
Each message appends its line; once the view passes the ceiling, one batch
merges the most due pairs, due = (T - last) / 2^l, oldest first on ties,
until it is at most the floor (gist §3.2). The compaction view is the view
merged further, with its own sawtooth; a compaction sees it up to its node
(gist §4).
-/

open scoped BigOperators

namespace EukheOptChat

-- THEORY
-- ======

-- Bool-valued equality (the model computes Bools, not Props)
def beq {α : Type} [DecidableEq α] (a b : α) : Bool := if a = b then true else false

-- Numbers
-- -------

-- 2^l
def pow2 (l : Nat) : Nat := 2 ^ l

-- x·2^l
def shl (l : Nat) (x : Nat) : Nat := x * 2 ^ l

-- the bit b added to x
def bit (b : Bool) (x : Nat) : Nat := if b then 1 + x else x

-- Bits
-- ----
-- A number in binary, lowest bit first, without high zero bits: 0 is [],
-- 6 is [false, true, true].

-- the value of the bits
def Bits.val (bs : List Bool) : Nat :=
  match bs with
  | [] => 0
  | h :: t => bit h (2 * Bits.val t)

-- x + 1
def Bits.inc (bs : List Bool) : List Bool :=
  match bs with
  | [] => [true]
  | false :: t => true :: t
  | true :: t => false :: Bits.inc t

-- the lowest bit (false for 0)
def Bits.low (bs : List Bool) : Bool :=
  match bs with | [] => false | h :: _ => h

-- the number halved (the bits above the lowest)
def Bits.up (bs : List Bool) : List Bool :=
  match bs with | [] => [] | _ :: t => t

-- x·2^l: l zero bits below x
def Bits.shl (l : Nat) (x : List Bool) : List Bool :=
  match l with
  | 0 => x
  | p + 1 => false :: Bits.shl p x

-- x + 1 when c holds
def Bits.inc_if (c : Bool) (x : List Bool) : List Bool :=
  if c then Bits.inc x else x

-- x + y + c
def Bits.add.go (xs ys : List Bool) (c : Bool) : List Bool :=
  match xs, ys with
  | [], _ => Bits.inc_if c ys
  | x :: xt, [] => Bits.inc_if c (x :: xt)
  | x :: xt, y :: yt =>
      Bool.xor (Bool.xor x y) c ::
        Bits.add.go xt yt (x ∧ y ∨ c ∧ (x ∨ y))

def Bits.add (xs ys : List Bool) : List Bool := Bits.add.go xs ys false

-- every bit false
def Bits.is_zero (xs : List Bool) : Bool :=
  match xs with
  | [] => true
  | h :: t => !h ∧ Bits.is_zero t

-- comparison
inductive Cmp where
  | lt | eq | gt
deriving DecidableEq

def Cmp.then (hi lo : Cmp) : Cmp :=
  match hi with
  | .eq => lo
  | .lt => .lt
  | .gt => .gt

def Cmp.of_zero (z : Bool) (ne : Cmp) : Cmp := if z then .eq else ne

def Cmp.is_lt (c : Cmp) : Bool := beq c .lt
def Cmp.is_eq (c : Cmp) : Bool := beq c .eq
def Cmp.is_gt (c : Cmp) : Bool := beq c .gt
def Cmp.is_le (c : Cmp) : Bool := Cmp.is_lt c ∨ Cmp.is_eq c

-- compare two bits
def Bool.cmp (x y : Bool) : Cmp :=
  if x = y then .eq else if x then .gt else .lt

-- the higher bits decide, unless equal
def Bits.cmp (xs ys : List Bool) : Cmp :=
  match xs, ys with
  | [], _ => Cmp.of_zero (Bits.is_zero ys) .lt
  | x :: xt, [] => Cmp.of_zero (Bits.is_zero (x :: xt)) .gt
  | x :: xt, y :: yt => Cmp.then (Bits.cmp xt yt) (Bool.cmp x y)

def Bits.gt (xs ys : List Bool) : Bool := Cmp.is_gt (Bits.cmp xs ys)
def Bits.le (xs ys : List Bool) : Bool := Cmp.is_le (Bits.cmp xs ys)
def Bits.same (xs ys : List Bool) : Bool := Cmp.is_eq (Bits.cmp xs ys)

-- a → b, as a Bool
def Bool.implies (a b : Bool) : Bool := if a then b else true

-- n > 0
def Nat.is_pos (n : Nat) : Bool := n > 0

-- Nodes
-- -----

-- node(l, i): the 2^l messages from i·2^l on
structure Node where
  l : Nat
  i : List Bool

def Node.lvl (n : Node) : Nat := n.l

-- id: the first message
def Node.start (n : Node) : Nat := shl n.l (Bits.val n.i)

-- n: how many messages
def Node.count (n : Node) : Nat := pow2 n.l

-- one past the last message
def Node.end (n : Node) : Nat := Node.start n + Node.count n

-- the node of message t
def Node.leaf (t : List Bool) : Node := ⟨0, t⟩

-- node(l+1, i/2)
def Node.parent (n : Node) : Node := ⟨n.l + 1, Bits.up n.i⟩

-- a and b are the two halves of one parent, a first
def Node.sib (a b : Node) : Bool :=
  beq a.l b.l && !Bits.low a.i && Bits.low b.i && beq (Bits.up a.i) (Bits.up b.i)

def Node.eq (a b : Node) : Bool :=
  beq a.l b.l && Bits.same a.i b.i

-- a before b: by level, then index
def Node.lt (a b : Node) : Bool :=
  if a.l < b.l then true else beq a.l b.l && Cmp.is_lt (Bits.cmp a.i b.i)

def Nodes.has (xs : List Node) (x : Node) : Bool :=
  match xs with
  | [] => false
  | h :: t => Node.eq h x ∨ Nodes.has t x

def Nodes.keep (k : Bool) (h : Node) (t : List Node) : List Node :=
  if k then h :: t else t

def Nodes.del (xs : List Node) (x : Node) : List Node :=
  match xs with
  | [] => []
  | h :: t => Nodes.keep (! (Node.eq h x)) h (Nodes.del t x)

def Nodes.ins.at (here same : Bool) (x h : Node) (t rec : List Node) : List Node :=
  match here, same with
  | true, _ => x :: h :: t
  | false, true => h :: t
  | false, false => h :: rec

-- x into the sorted xs, once
def Nodes.ins (xs : List Node) (x : Node) : List Node :=
  match xs with
  | [] => [x]
  | h :: t => Nodes.ins.at (Node.lt x h) (Node.eq x h) x h t (Nodes.ins t x)

def Nodes.add (xs : List Node) (x : Node) : List Node :=
  Nodes.keep (! (Nodes.has xs x)) x xs

-- the other half of n's parent
def Bits.flip (bs : List Bool) : List Bool :=
  match bs with
  | [] => [true]
  | false :: t => true :: t
  | true :: t =>
    match t with
    | [] => []
    | h :: r => false :: h :: r

def Node.sibling (n : Node) : Node := ⟨n.l, Bits.flip n.i⟩

-- Built nodes
-- -----------

inductive Trie where
  | tip
  | bin (val : Option Nat) (lo hi : Trie)

def Trie.get (k : List Bool) (t : Trie) : Option Nat :=
  match k, t with
  | _, .tip => none
  | [], .bin v _ _ => v
  | false :: r, .bin _ lo _ => Trie.get r lo
  | true :: r, .bin _ _ hi => Trie.get r hi

def Trie.set (k : List Bool) (t : Trie) (s : Nat) : Trie :=
  match k, t with
  | [], .tip => .bin (some s) .tip .tip
  | [], .bin _ lo hi => .bin (some s) lo hi
  | false :: r, .tip => .bin none (Trie.set r .tip s) .tip
  | true :: r, .tip => .bin none .tip (Trie.set r .tip s)
  | false :: r, .bin v lo hi => .bin v (Trie.set r lo s) hi
  | true :: r, .bin v lo hi => .bin v lo (Trie.set r hi s)

inductive Info where
  | all (size : Nat)
  | lvls (ts : List Trie)

def Lvls.get (l : Nat) (ts : List Trie) (k : List Bool) : Option Nat :=
  match l, ts with
  | _, [] => none
  | 0, h :: _ => Trie.get k h
  | p + 1, _ :: t => Lvls.get p t k

def Lvls.set (l : Nat) (ts : List Trie) (k : List Bool) (s : Nat) : List Trie :=
  match l, ts with
  | 0, [] => [Trie.set k .tip s]
  | 0, h :: t => Trie.set k h s :: t
  | p + 1, [] => .tip :: Lvls.set p [] k s
  | p + 1, h :: t => h :: Lvls.set p t k s

def Info.empty : Info := .lvls []

-- the node's size, when it is built
def Info.get (info : Info) (n : Node) : Option Nat :=
  match info with
  | .all s => some s
  | .lvls ts => Lvls.get n.l ts n.i

-- node n is built, s bytes
def Info.set (info : Info) (n : Node) (s : Nat) : Info :=
  match info with
  | .all a => .all a
  | .lvls ts => .lvls (Lvls.set n.l ts n.i s)

def Info.built (info : Info) (n : Node) : Bool :=
  match Info.get info n with
  | none => false
  | some _ => true

-- The chat
-- --------

structure Cfg where
  ph : Nat
  ceil : Nat
  floor : Nat
  cceil : Nat
  cfloor : Nat
  jobs : Nat

-- T (in binary), the built nodes, the view, whether a batch is still
-- shrinking it, the compaction view, the ready merges, and the nodes being
-- built
structure St where
  t : List Bool
  info : Info
  view : List Node
  shrink : Bool
  cview : List Node
  ready : List Node
  busy : List Node

def St.empty : St := ⟨[], Info.empty, [], false, [], [], []⟩

-- What happens to the chat: a message is logged; a node is built (s bytes);
-- a node's call starts; a call fails (its node may start again).
inductive Ev where
  | msg
  | build (n : Node) (size : Nat)
  | start (n : Node)
  | free (n : Node)

-- The reference batch
-- --------------------

-- a line counts its node's bytes, or the placeholder's while unbuilt
def size.of (ph : Nat) (m : Option Nat) : Nat := m.getD ph

def line_size (ph : Nat) (info : Info) (n : Node) : Nat :=
  size.of ph (Info.get info n)

def view_size (ph : Nat) (info : Info) (v : List Node) : Nat :=
  match v with
  | [] => 0
  | h :: t => line_size ph info h + view_size ph info t

-- the due measure: Last from the pair's last message, First from its first
inductive Age where
  | last | first

-- e: one past the pair's last message, (i+2)·2^l; s: its first, i·2^l
def pair_end (a : Node) : List Bool := Bits.shl a.l (Bits.inc (Bits.inc a.i))
def pair_start (a : Node) : List Bool := Bits.shl a.l a.i

-- the pair from a on is more due than the pair from b on
def more_due.cross (u : List Bool) (la lb : Nat) (xa xb : List Bool) : Bool :=
  Bits.gt (Bits.add (Bits.shl lb u) (Bits.shl la xb))
          (Bits.add (Bits.shl la u) (Bits.shl lb xa))

def more_due (m : Age) (t : List Bool) (a b : Node) : Bool :=
  match m with
  | .last => more_due.cross (Bits.inc t) a.l b.l (pair_end a) (pair_end b)
  | .first => more_due.cross t a.l b.l (pair_start a) (pair_start b)

-- a and b may merge: they are the halves of a built parent
def mergeable (info : Info) (a b : Node) : Bool :=
  Node.sib a b && Info.built info (Node.parent a)

-- a and the next line (if any) may merge
def pair.ok (info : Info) (a : Node) (next : Option Node) : Bool :=
  match next with
  | none => false
  | some b => mergeable info a b

def best.vs (more : Bool) (a c : Node) : Node := if more then a else c

def best.take (m : Age) (t : List Bool) (a : Node) (cur : Option Node) : Option Node :=
  match cur with
  | none => some a
  | some c => some (best.vs (more_due m t a c) a c)

def best.pick (ok : Bool) (m : Age) (t : List Bool) (a : Node) (cur : Option Node) : Option Node :=
  if ok then best.take m t a cur else cur

def best.pair (m : Age) (t : List Bool) (info : Info) (a : Node)
    (next : Option Node) (cur : Option Node) : Option Node :=
  match next with
  | none => cur
  | some b => best.pick (mergeable info a b) m t a cur

def headOpt (xs : List α) : Option α :=
  match xs with | [] => none | x :: _ => some x

-- scan the pairs oldest first; a later pair wins only when strictly more due
def best.go (m : Age) (t : List Bool) (info : Info) (v : List Node)
    (cur : Option Node) : Option Node :=
  match v with
  | [] => cur
  | a :: rest => best.go m t info rest (best.pair m t info a (headOpt rest) cur)

-- the first line of the most due mergeable pair, if any
def best (m : Age) (t : List Bool) (info : Info) (v : List Node) : Option Node :=
  best.go m t info v none

-- Merging
-- -------

def merge.pick (hit : Bool) (x _y : Node) (more rec : List Node) : List Node :=
  if hit then Node.parent x :: more else x :: rec

def merge.here (info : Info) (a x : Node) (rest rec : List Node) : List Node :=
  match rest with
  | [] => [x]
  | y :: more => merge.pick (Node.eq x a && mergeable info x y) x y more rec

-- the first pair (a, y) of v that may merge, replaced by its parent
def merge (info : Info) (v : List Node) (a : Node) : List Node :=
  match v with
  | [] => []
  | x :: rest => merge.here info a x rest (merge info rest a)

def chooseNextIf (over : Bool) (m : Age) (t : List Bool) (info : Info)
    (v : List Node) : Option Node :=
  if over then best m t info v else none

-- the next merge of a fit: the most due pair, while over budget
def chooseNext (m : Age) (t : List Bool) (budget ph : Nat) (info : Info)
    (v : List Node) : Option Node :=
  chooseNextIf (view_size ph info v > budget) m t info v

def fit.cons (n : Node) (r : List Node × List Node) : List Node × List Node :=
  let (ms, out) := r; (n :: ms, out)

-- merge the most due pair whose parent is built, and repeat, until the view
-- fits the budget or no pair can merge; c is the next merge. Returns the
-- merged parents, in merge order, and the view.
def fit.go (fuel : Nat) (c : Option Node) (m : Age) (t : List Bool)
    (budget ph : Nat) (info : Info) (v : List Node) : List Node × List Node :=
  match fuel, c with
  | 0, _ => ([], v)
  | _f + 1, none => ([], v)
  | f + 1, some a =>
      let w := merge info v a
      fit.cons (Node.parent a) (fit.go f (chooseNext m t budget ph info w) m t budget ph info w)

-- fit the view of T messages into budget bytes; the view's length bounds the
-- merges
def fit (m : Age) (t : List Bool) (budget ph : Nat) (info : Info)
    (v : List Node) : List Node × List Node :=
  fit.go v.length (chooseNext m t budget ph info v) m t budget ph info v

def fit.view (m : Age) (t : List Bool) (budget ph : Nat) (info : Info)
    (v : List Node) : List Node :=
  (fit m t budget ph info v).2

-- Taelin's rollback push
-- ----------------------

structure Entry where
  keep : Nat
  life : Nat
  state : List Bool

def push (states : List Entry) (s : List Bool) : List Entry :=
  match states with
  | [] => [⟨0, 0, s⟩]
  | e :: older =>
    match e.keep with
    | 0 => ⟨1, e.life, e.state⟩ :: older
    | k + 1 =>
      match e.life with
      | l + 1 => ⟨0, 0, s⟩ :: ⟨0, l, e.state⟩ :: older
      | 0 => ⟨0, 0, s⟩ :: push older e.state

def Bitss.same (as bs : List (List Bool)) : Bool :=
  match as, bs with
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys => Bits.same x y && Bitss.same xs ys

-- the view is push's list, oldest first: each state starts a line
def starts (v : List Node) : List (List Bool) :=
  match v with
  | [] => []
  | h :: t => pair_start h :: starts t

def states (es : List Entry) : List (List Bool) :=
  match es with
  | [] => []
  | e :: t => e.state :: states t

def same_lines (v : List Node) (es : List Entry) : Bool :=
  Bitss.same (starts v) (states es).reverse

-- Push t = 0..n-1, one message each; the view appends each message and fits
-- push's list length (every line 1 byte, every node built). True when the
-- two agree after every push.
def agree.go (n : Nat) (m : Age) (tb : List Bool) (es : List Entry)
    (v : List Node) : Bool :=
  match n with
  | 0 => true
  | p + 1 =>
    let es2 := push es tb
    let tb2 := Bits.inc tb
    let v2 := fit.view m tb2 es2.length 0 (Info.all 1) (v ++ [Node.leaf tb])
    same_lines v2 es2 && agree.go p m tb2 es2 v2

def agree (m : Age) (n : Nat) : Bool := agree.go n m [] [] []

-- The reference step
-- -------------------

-- the compaction view: past cceil, it merges down to cfloor
def fitc.if (over : Bool) (cfg : Cfg) (t : List Bool) (info : Info)
    (cv : List Node) : List Node :=
  if over then fit.view Age.last t cfg.cfloor cfg.ph info cv else cv

def fitc (cfg : Cfg) (t : List Bool) (info : Info) (cv : List Node) : List Node :=
  fitc.if (view_size cfg.ph info cv > cfg.cceil) cfg t info cv

-- a message
def msg.cview (merged : List Node) (cfg : Cfg) (t : List Bool) (info : Info)
    (view cv : List Node) : List Node :=
  match merged with
  | [] => fitc cfg t info cv
  | _ :: _ => fit.view Age.last t cfg.cfloor cfg.ph info view

def msg.after (merged view : List Node) (cfg : Cfg) (t : List Bool) (info : Info)
    (cv ready busy : List Node) : St × List Node :=
  (⟨t, info, view, view_size cfg.ph info view > cfg.floor,
     msg.cview merged cfg t info view cv, ready, busy⟩, merged)

def msg.batch (r : List Node × List Node) (cfg : Cfg) (t : List Bool) (info : Info)
    (cv ready busy : List Node) : St × List Node :=
  let (merged, view) := r
  msg.after merged view cfg t info cv ready busy

def msg.go (grow : Bool) (cfg : Cfg) (t : List Bool) (info : Info)
    (view cv ready busy : List Node) : St × List Node :=
  if grow then
    msg.batch (fit Age.last t cfg.floor cfg.ph info view) cfg t info cv ready busy
  else
    (⟨t, info, view, false, fitc cfg t info cv, ready, busy⟩, [])

-- the view with message t's line
def St.grown (s : St) : List Node := s.view ++ [Node.leaf s.t]

-- a batch runs (or goes on) at this message
def St.batch (cfg : Cfg) (s : St) : Bool :=
  s.shrink ∨ view_size cfg.ph s.info (St.grown s) > cfg.ceil

-- message T arrives: the state after it, and the batch it set off
def msg (cfg : Cfg) (s : St) : St × List Node :=
  msg.go (St.batch cfg s) cfg (Bits.inc s.t) s.info (St.grown s)
    (s.cview ++ [Node.leaf s.t]) s.ready s.busy

-- a built node
def ready.if (go : Bool) (p : Node) (rs : List Node) : List Node :=
  if go then Nodes.ins rs p else rs

def ready.note (info : Info) (n : Node) (rs : List Node) : List Node :=
  ready.if (Info.built info (Node.sibling n) && !Info.built info (Node.parent n))
    (Node.parent n) rs

def build.go (cfg : Cfg) (n : Node) (info : Info) (s : St) : St :=
  { s with info := info,
          cview := fitc cfg s.t info s.cview,
          ready := ready.note info n (Nodes.del s.ready n),
          busy := Nodes.del s.busy n }

def build (cfg : Cfg) (s : St) (n : Node) (size : Nat) : St :=
  build.go cfg n (Info.set s.info n size) s

def busy.set (s : St) (bs : List Node) : St := { s with busy := bs }

-- one event: the state after it, and the batch it set off
def step (cfg : Cfg) (s : St) (e : Ev) : St × List Node :=
  match e with
  | .msg => msg cfg s
  | .build n size => (build cfg s n size, [])
  | .start n => (busy.set s (Nodes.add s.busy n), [])
  | .free n => (busy.set s (Nodes.del s.busy n), [])

def run.go (evs : List Ev) (cfg : Cfg) (s : St) : St :=
  match evs with
  | [] => s
  | e :: rest => run.go rest cfg (step cfg s e).1

-- the chat after evs, from an empty one
def run (cfg : Cfg) (evs : List Ev) : St := run.go evs cfg St.empty

-- A compaction's view
-- --------------------

def Node.end_bits (n : Node) : List Bool := Bits.shl n.l (Bits.inc n.i)

def ctx.bound (n : Node) : List Bool :=
  match n.l with
  | 0 => n.i
  | p + 1 => Bits.shl (p + 1) (Bits.inc n.i)

def ctx.keep (k : Bool) (h : Node) (rec : List Node) : List Node :=
  if k then h :: rec else []

-- a line stays when it ends by the bound and is built
def ctx.ok (info : Info) (bound : List Bool) (h : Node) : Bool :=
  Bits.le (Node.end_bits h) bound && Info.built info h

def ctx.go (v : List Node) (info : Info) (bound : List Bool) : List Node :=
  match v with
  | [] => []
  | h :: rest => ctx.keep (ctx.ok info bound h) h (ctx.go rest info bound)

-- the view a compaction of node n sees
def ctx (s : St) (n : Node) : List Node := ctx.go s.cview s.info (ctx.bound n)

-- The work queue
-- --------------

def cand.emit (stop built free : Bool) (h : Node) (rec : List Node) : List Node :=
  match stop, built, free with
  | true, _, _ => []
  | false, true, _ => rec
  | false, false, true => h :: rec
  | false, false, false => rec

-- the view's unbuilt lines that may start: unb unbuilt lines seen, room free
def cand.view (v : List Node) (info : Info) (busy : List Node) (jobs : Nat)
    (unb : Nat) (room : Nat) : List Node :=
  match v, room with
  | [], _ => []
  | _ :: _, 0 => []
  | h :: rest, r + 1 =>
    let built := Info.built info h
    let free := !Nodes.has busy h
    cand.emit (unb ≥ jobs) built free h
      (cand.view rest info busy jobs (unb + (if built then 0 else 1))
        (r + 1 - (if built ∨ !free then 0 else 1)))

def cand.ready (rs : List Node) (busy : List Node) (room : Nat) : List Node :=
  match rs, room with
  | [], _ => []
  | _ :: _, 0 => []
  | h :: rest, r + 1 =>
    let free := !Nodes.has busy h
    Nodes.keep free h (cand.ready rest busy (r + 1 - (if free then 1 else 0)))

def cands.with (s : St) (room : Nat) (c0 : List Node) : List Node :=
  c0 ++ cand.ready s.ready s.busy (room - c0.length)

-- the nodes to start now, oldest message first, then the ready merges
def cands (cfg : Cfg) (s : St) : List Node :=
  let room := cfg.jobs - s.busy.length
  cands.with s room (cand.view s.view s.info s.busy cfg.jobs 0 room)

-- the nodes to start while a turn waits for the view: the view's unbuilt
-- lines only, oldest first
def cands.need (cfg : Cfg) (s : St) : List Node :=
  cand.view s.view s.info s.busy cfg.jobs 0 (cfg.jobs - s.busy.length)

-- the busy nodes that are view lines still unbuilt
def busy.need (info : Info) (v : List Node) (bs : List Node) : List Node :=
  match bs with
  | [] => []
  | b :: rest => Nodes.keep (Nodes.has v b && !Info.built info b) b (busy.need info v rest)

-- a turn starts to wait: every call of a node it does not need stops
def St.wait (s : St) : St := { s with busy := busy.need s.info s.view s.busy }

-- the compactor's settle: some line of v is neither built nor busy
def idle (info : Info) (v : List Node) (busy : List Node) : Bool :=
  match v with
  | [] => false
  | h :: rest => (!Info.built info h && !Nodes.has busy h) ∨ idle info rest busy

-- What the laws speak of
-- ----------------------

-- Tiles(s, v, e): the lines of v cover the messages s..e-1, each message
-- once, contiguous, oldest first
def Tiles (s : Nat) (v : List Node) (e : Nat) : Prop :=
  match v with
  | [] => s = e
  | h :: t => Node.start h = s ∧ Tiles (s + Node.count h) t e

-- Here(info, x, rest, z, w): x and the first line of rest are the two halves
-- of a built parent z, and w is the rest after them
def Here (info : Info) (x : Node) (rest : List Node) (z : Node)
    (w : List Node) : Prop :=
  match rest with
  | [] => False
  | y :: more => mergeable info x y ∧ z = Node.parent x ∧ w = more

-- Merged(info, v, w): w is v with one pair of sibling lines replaced by
-- their built parent, and nothing else changed
def Merged (info : Info) (v w : List Node) : Prop :=
  match v, w with
  | [], _ => False
  | _ :: _, [] => False
  | x :: vr, z :: wr => Here info x vr z wr ∨ (x = z ∧ Merged info vr wr)

-- some pair of adjacent lines may merge (its parent is built)
def can_merge (info : Info) (v : List Node) : Bool :=
  match v with
  | [] => false
  | x :: rest => pair.ok info x (headOpt rest) ∨ can_merge info rest

-- every node of v is built
def Built (info : Info) (v : List Node) : Prop :=
  match v with
  | [] => True
  | h :: t => Info.built info h ∧ Built info t

-- every line of v that merges messages (level above 0) is built; a message's
-- own line may wait for its summary
def Summarized (info : Info) (v : List Node) : Prop :=
  match v with
  | [] => True
  | h :: t => (Node.lvl h > 0 → Info.built info h) ∧ Summarized info t

-- every line of v ends by message b (in binary), and is built
def Before (info : Info) (b : List Bool) (v : List Node) : Prop :=
  match v with
  | [] => True
  | h :: t => Bits.le (Node.end_bits h) b ∧ Info.built info h ∧ Before info b t

-- p is a prefix of v
def Prefix (p v : List Node) : Prop :=
  match p, v with
  | [], _ => True
  | _ :: _, [] => False
  | x :: pr, y :: vr => x = y ∧ Prefix pr vr

-- bs has no high zero bit: its last bit, if any, is true
def Bits.canon.go (t : List Bool) (h : Bool) : Bool :=
  match t with | [] => h | x :: r => Bits.canon.go r x

def Bits.canon (bs : List Bool) : Bool :=
  match bs with | [] => true | h :: t => Bits.canon.go t h

-- every line of v has an index without a high zero bit
def Canon (v : List Node) : Bool :=
  match v with
  | [] => true
  | ⟨l, i⟩ :: rest => Bits.canon i && Canon rest

def view.of (cfg : Cfg) (evs : List Ev) : List Node := (run cfg evs).view
def cview.of (cfg : Cfg) (evs : List Ev) : List Node := (run cfg evs).cview
def total.of (cfg : Cfg) (evs : List Ev) : Nat := Bits.val (run cfg evs).t

-- the gist's example: T = 10, the view 0+4, 4+4, 8+1, 9+1
def ten : List Bool := [false, true, false, true]
def view10 : List Node :=
  [⟨2, []⟩, ⟨2, [true]⟩, ⟨0, [false, false, false, true]⟩, ⟨0, [true, false, false, true]⟩]

end EukheOptChat

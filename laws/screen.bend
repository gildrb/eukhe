# eukhe: the laws of area screen

import Base
import ../bend/ffi_screen.bend as FSc
import ../bend/run/recovery.bend as RnRecovery
import ../bend/screen.bend as Sc
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S8) The interface
# ------------------
# the model in bend/screen.bend. Every input is free:
# any blocks, growths, finals, flushes and resizes in any order; any
# chunk sizes and frames; any check results; any child heights.

# LAW tx_gapless: committed blocks come first: the scrollback has no gap
law tx_gapless:
  for es: List<&2, Sc.Ev>
  for +w: Nat
  {Sc.gapless(Sc.Tx.blocks(Sc.run(es, Sc.Tx{Nil{}, 0n, w}))) == True{} : Bool}

# LAW tx_scrollback_append_only: the scrollback only grows: what is committed stays, unchanged, in
# its place, whatever comes after
law tx_scrollback_append_only:
  for +pre: List<&2, Sc.Ev>
  for post: List<&2, Sc.Ev>
  for +w: Nat
  {Sc.pre(Sc.scroll(Sc.Tx.blocks(Sc.run(pre, Sc.Tx{Nil{}, 0n, w}))), Sc.scroll(Sc.Tx.blocks(Sc.run(List.append(&2, Sc.Ev, pre, post), Sc.Tx{Nil{}, 0n, w})))) == True{} : Bool}

# LAW tx_resize_keeps: a resize writes no block again
law tx_resize_keeps:
  for +t: Sc.Tx
  for +w: Nat
  {Sc.Tx.blocks(Sc.step(t, Sc.Resize{w})) == Sc.Tx.blocks(t) : List<&2, Sc.Blk>}

# LAW tx_flush_settles: after a flush no final block waits: the first block not committed
# is active
law tx_flush_settles:
  for +t: Sc.Tx
  {Sc.flushed(Sc.Tx.blocks(Sc.step(t, Sc.Flush{}))) == True{} : Bool}

# LAW pace_never_ahead: the screen never shows text that did not arrive
law pace_never_ahead:
  for es: List<&2, Sc.PEv>
  for +min: Nat
  for +k: Nat
  {Nat.is_le(Sc.Pace.shown(Sc.pace.run(es, min, k, Sc.Pace{0n, 0n})), Sc.Pace.recv(Sc.pace.run(es, min, k, Sc.Pace{0n, 0n}))) == True{} : Bool}

# LAW pace_never_back: the screen never shows less than before
law pace_never_back:
  for +min: Nat
  for +k: Nat
  for +p: Sc.Pace
  for e: Sc.PEv
  {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.shown(Sc.pace.step(min, k, p, e))) == True{} : Bool}

# LAW pace_drains: with a minimum of at least 1, a backlog of b characters is all
# shown after b frames
law pace_drains:
  for +min: Nat
  for +k: Nat
  for +p: Sc.Pace
  for +n: Nat
  for one: {Nat.is_le(1n, min) == True{} : Bool}
  for behind: {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.recv(p)) == True{} : Bool}
  for enough: {Nat.is_le(Nat.sub(Sc.Pace.recv(p), Sc.Pace.shown(p)), n) == True{} : Bool}
  {Sc.Pace.shown(Sc.pace.run(Sc.frames(n), min, k, p)) == Sc.Pace.recv(p) : Nat}

# LAW verify_only_checked: only a frame that passed its check reaches the terminal, and a
# frame that failed both checks is reported
law verify_only_checked:
  for f: Nat
  for g: Nat
  for +ok1: Bool
  for +ok2: Bool
  {Sc.checked(Sc.present(f, g, ok1, ok2), ok1, ok2) == True{} : Bool}

# spec: the first of the three checks that passes picks the frame drawn
# (the frame f, its full redraw g, its fresh redraw h on a blank screen);
# when none passes nothing is drawn and the first frame is kept
def screen_paint_spec(f: Nat, g: Nat, h: Nat, ok1: Bool, ok2: Bool, ok3: Bool) -> Sc.Paint:
  match ok1:
    case True{}:
      Sc.Put{f, False{}}
    case False{}:
      match ok2:
        case True{}:
          Sc.Put{g, True{}}
        case False{}:
          match ok3:
            case True{}:
              Sc.Fresh{h}
            case False{}:
              Sc.Kept{f}

# LAW paint_first_passing_check: the screen never stops: the first check that passes picks what
# reaches the terminal (the frame, its full redraw, its fresh redraw on a
# blank screen); when all three fail nothing is drawn, the first frame is
# kept, and the surface goes on
# EXCLUDES: a frame drawn after its check failed; a passing redraw left
# unused; a fresh redraw before both checks failed; an end of the surface
# (or any outcome but Kept) after three failed checks
law paint_first_passing_check:
  for +f: Nat
  for +g: Nat
  for +h: Nat
  for +ok1: Bool
  for +ok2: Bool
  for +ok3: Bool
  {Sc.resync(Sc.present(f, g, ok1, ok2), h, ok3) == screen_paint_spec(f, g, h, ok1, ok2, ok3) : Sc.Paint}

# LAW layout_inside: no child is drawn outside the viewport
law layout_inside:
  for hs: List<&2, Nat>
  for +y: Nat
  for +rows: Nat
  {Sc.inside(Sc.vstack(hs, y, rows), rows) == True{} : Bool}

# LAW layout_apart: no two children overlap
law layout_apart:
  for hs: List<&2, Nat>
  for +y: Nat
  for +rows: Nat
  {Sc.apart(Sc.vstack(hs, y, rows), y) == True{} : Bool}

# LAW layout_whole_when_room: children that fit are drawn whole
law layout_whole_when_room:
  for +hs: List<&2, Nat>
  for +y: Nat
  for +rows: Nat
  for fits: {Nat.is_le(Nat.add(y, Sc.sum(hs)), rows) == True{} : Bool}
  {Sc.heights(Sc.vstack(hs, y, rows)) == hs : List<&2, Nat>}

# LAW pace_reveal_formula: the guarded share is the plain formula, for every minimum, lag and
# backlog: a frame reveals min(b, max(min, b / (1 + k)))
# EXCLUDES: a guard (no 1 + k formed when k >= b) that changes the
# reveal for some lag
law pace_reveal_formula:
  for +min: Nat
  for +k: Nat
  for +b: Nat
  {Sc.reveal(min, k, b) == Nat.min(b, Nat.max(min, Nat.div(b, 1n+k))) : Nat}

# LAW pace_lag_at_cap: a lag at least the backlog reveals the minimum (the whole backlog
# when it is smaller). Rust saturates the lag at the cap of the compiled
# core's numbers (2^48 - 1), which is at least every backlog it holds: a
# lag at the cap reveals the minimum
# EXCLUDES: a capped lag that reveals more than the minimum, or nothing
law pace_lag_at_cap:
  for +min: Nat
  for +k: Nat
  for +b: Nat
  for capped: {Nat.is_le(b, k) == True{} : Bool}
  {Sc.reveal(min, k, b) == Nat.min(b, min) : Nat}

# every block of bs is committed
def all_comm(bs: List<&2, Sc.Blk>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case b <> rest:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              all_comm(rest)
            case Sc.Final{}:
              False{}
            case Sc.Active{}:
              False{}

# the transcript t with the blocks cs before its blocks
def under(cs: List<&2, Sc.Blk>, t: Sc.Tx) -> Sc.Tx:
  match t:
    case Sc.Tx{bs, n, w}:
      Sc.Tx{List.append(&2, Sc.Blk, cs, bs), n, w}

# LAW tx_committed_inert: committed blocks are inert. Any events on a transcript whose
# blocks start with committed blocks cs give the transcript the same
# events give without cs, with cs in front. So the core runs on the blocks
# after the committed prefix alone (Rust sends only those)
# EXCLUDES: an event that changes, drops or moves a committed block, and
# a result that depends on the committed blocks
law tx_committed_inert:
  for es: List<&2, Sc.Ev>
  for +cs: List<&2, Sc.Blk>
  for +bs: List<&2, Sc.Blk>
  for +n: Nat
  for +w: Nat
  for comm: {all_comm(cs) == True{} : Bool}
  {Sc.run(es, Sc.Tx{List.append(&2, Sc.Blk, cs, bs), n, w}) == under(cs, Sc.run(es, Sc.Tx{bs, n, w})) : Sc.Tx}

# LAW all_comm_example: the premise of tx_committed_inert holds for a real prefix
# EXCLUDES: an all_comm that is never True (a vacuous inert law)
law all_comm_example:
  {all_comm([Sc.Blk{0n, Sc.Comm{}, 3n}, Sc.Blk{1n, Sc.Comm{}, 0n}]) == True{} : Bool}

# LAW all_comm_rejects: a prefix with a final or an active block is not committed
# EXCLUDES: an all_comm that is always True
law all_comm_rejects:
  {Bool.or(all_comm([Sc.Blk{0n, Sc.Final{}, 0n}]), all_comm([Sc.Blk{0n, Sc.Comm{}, 0n}, Sc.Blk{1n, Sc.Active{}, 0n}])) == False{} : Bool}

# ---- recover ----

# LAWS (H4.8): a stuck model gets a recovery. Each law is an open claim
# about the model in bend/run/recovery.bend; PROOF.bend proves them (as Screen.<law>)
# with the lemmas of proof/screen/.

# (H4.8) A stuck model gets a recovery, each with a cap
# -----------------------------------------------------
# LAWS.bend H4.8, the recoveries of bend/run/recovery.bend (Rec): a length
# stop while the model still reasons, tool calls leaked as text, the same
# tool calls with the same results round after round. Every reply is
# free, in any order. A Redo is a noted error, so its retry ends its
# request with a new note (H4.7); the laws of H4 hold for every reply, so
# they hold for the reply a recovery makes. A recovery does not depend on
# the retry policy: a note is a new request, not a transient error.

# LAW rec_length_retries_with_a_note: a length stop with no answer under the cap (fewer than `long`
# length notes in a row) is retried with the next length note
law rec_length_retries_with_a_note:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for under: {RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)) == True{} : Bool}
  {RnRecovery.Rec.step(rc, RnRecovery.Long{}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+RnRecovery.Rk.longs(k, row), same, last}} : RnRecovery.Dec}

# LAW rec_leak_retries_with_a_note: leaked calls that were not rebuilt, under the cap, are retried with
# the next leak note
law rec_leak_retries_with_a_note:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for under: {RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)) == True{} : Bool}
  {RnRecovery.Rec.step(rc, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+RnRecovery.Rk.leaks(k, row), same, last}} : RnRecovery.Dec}

# LAW rec_length_row_exact: the length notes in a row that the next request's note counts
# are its row when it is a length note, else 0 (decide.rs `NoteCause::row`)
# EXCLUDES: a count of length notes that stays 0 or resets, so the cap of
#   rec_length_retries_with_a_note is never reached; a row of another
#   recovery counted as length notes
law rec_length_row_exact:
  for +row: Nat
  {[RnRecovery.Rk.longs(RnRecovery.Free{}, row), RnRecovery.Rk.longs(RnRecovery.Longs{}, row), RnRecovery.Rk.longs(RnRecovery.Leaks{}, row), RnRecovery.Rk.longs(RnRecovery.Loops{}, row), RnRecovery.Rk.longs(RnRecovery.Empties{}, row)] == [0n, row, 0n, 0n, 0n] : List<&2, Nat>}

# LAW rec_leak_row_exact: the leak notes in a row that the next request's note counts are
# its row when it is a leak note, else 0 (decide.rs `NoteCause::row`)
# EXCLUDES: a count of leak notes that stays 0 or resets, so the cap of
#   rec_leak_retries_with_a_note is never reached; a row of another
#   recovery counted as leak notes
law rec_leak_row_exact:
  for +row: Nat
  {[RnRecovery.Rk.leaks(RnRecovery.Free{}, row), RnRecovery.Rk.leaks(RnRecovery.Longs{}, row), RnRecovery.Rk.leaks(RnRecovery.Leaks{}, row), RnRecovery.Rk.leaks(RnRecovery.Loops{}, row), RnRecovery.Rk.leaks(RnRecovery.Empties{}, row)] == [0n, 0n, row, 0n, 0n] : List<&2, Nat>}

# ---- screen: the entry ----

# LAWS (S8, the compiled core): the interface's rules run as the model of
# bend/screen.bend through the compiled core's entry bend/ffi_screen.bend
# (crates/eukhe-tui: view/ledger.rs, pace.rs, view/stack.rs). The laws of
# the model itself are in the first section, (S8) The interface. Every
# input is free: any transcript, events, pace, rate and heights whose
# numbers fit the wire.

# The compiled core's entry of the interface (bend/ffi_screen.bend): Rust
# writes a request with FSc.put_req and reads the reply; every Nat of a
# request fits the wire (at most 14 digits, wire_fits)

# every Nat of a block fits the wire
def blk_fits(b: Sc.Blk) -> Bool:
  match b:
    case Sc.Blk{i, s, l}:
      Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(l))

def blks_fit(bs: List<&2, Sc.Blk>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, t}:
      Bool.and(blk_fits(b), blks_fit(t))

# every Nat of an event fits the wire
def ev_fits(e: Sc.Ev) -> Bool:
  match e:
    case Sc.Open{}:
      True{}
    case Sc.Grow{x, n}:
      Bool.and(LawsBase.wire_fits(x), LawsBase.wire_fits(n))
    case Sc.Fin{x}:
      LawsBase.wire_fits(x)
    case Sc.Flush{}:
      True{}
    case Sc.Resize{w}:
      LawsBase.wire_fits(w)

def evs_fit(es: List<&2, Sc.Ev>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(ev_fits(e), evs_fit(t))

# every Nat of a transcript fits the wire, its block count too
def tx_fits(t: Sc.Tx) -> Bool:
  match t:
    case Sc.Tx{+bs, n, w}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Sc.Blk, bs)), Bool.and(blks_fit(bs), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(w))))

# LAW screen_ffi_run: the entry runs a frame's events as the model: the reply to a Run
# request is the transcript Sc.run gives, encoded
# EXCLUDES: an entry that misreads a block, an event or the order of the
# events, that drops or invents an event, or answers another transcript
law screen_ffi_run:
  for +t: Sc.Tx
  for +es: List<&2, Sc.Ev>
  for +ft: {tx_fits(t) == True{} : Bool}
  for +fe: {Bool.and(LawsBase.wire_fits(List.length(&2, Sc.Ev, es)), evs_fit(es)) == True{} : Bool}
  {FSc.ffi(FSc.put_req(FSc.ReqRun{t, es}, "")) == FSc.put_tx(Sc.run(es, t), "") : String}

# LAW screen_ffi_pace: the entry paces a frame as the model: n characters arrive, then a
# frame shows its share
# EXCLUDES: an entry that swaps the minimum and the lag, reads recv and
# shown the wrong way round, or frames before the characters arrive
law screen_ffi_pace:
  for +min: Nat
  for +k: Nat
  for +r: Nat
  for +s: Nat
  for +n: Nat
  for +f: {Bool.and(Bool.and(LawsBase.wire_fits(min), LawsBase.wire_fits(k)), Bool.and(Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(s)), LawsBase.wire_fits(n))) == True{} : Bool}
  {FSc.ffi(FSc.put_req(FSc.ReqPace{min, k, Sc.Pace{r, s}, n}, "")) == FSc.put_pace(Sc.pace.run([Sc.Chunk{n}, Sc.Frame{}], min, k, Sc.Pace{r, s}), "") : String}

# LAW screen_ffi_stack: the entry stacks children as the model
# EXCLUDES: an entry that misreads a height, the start row or the rows
law screen_ffi_stack:
  for +hs: List<&2, Nat>
  for +y: Nat
  for +rows: Nat
  for +f: {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)), Bool.and(LawsBase.wire_fits(y), LawsBase.wire_fits(rows))) == True{} : Bool}
  {FSc.ffi(FSc.put_req(FSc.ReqStack{hs, y, rows}, "")) == Wr.put_list(~Sc.Rect, ~FSc.put_rect, Sc.vstack(hs, y, rows), "") : String}

# LAW screen_ffi_example: the requests Rust writes, as text: a frame (blocks 5 and 6 live,
# open one, finish 5, flush), a pace frame and a stack, with their replies
# EXCLUDES: a request or reply format other than WIRE.md's (tags, field
# order, counts)
law screen_ffi_example:
  {[FSc.ffi("0,2,5,0,0,6,0,0,7,80,3,0,2,5,3,"), FSc.ffi("1,2,3,0,0,400,"), FSc.ffi("2,3,2,3,4,1,5,")] == ["3,5,2,0,6,0,0,7,0,0,8,80,", "400,100,", "3,1,2,3,2,6,0,"] : List<&2, String>}

# LAW screen_ffi_refuses_example: a malformed request or one with input left over answers the error
# form, never a reply
# EXCLUDES: a default reply to a request the entry could not read
law screen_ffi_refuses_example:
  {[FSc.ffi("7,"), FSc.ffi("2,0,0,0,x"), FSc.ffi("1,2,3,0,0,01,")] == [Wr.err("screen: malformed request"), Wr.err("screen: input left over"), Wr.err("screen: malformed request")] : List<&2, String>}

# The paint decision (inline_term.rs `paint_decision`): Rust runs a
# frame's check and asks the entry with the checks run so far, in order;
# the entry answers the paint, or asks for the next check (the full
# redraw's, then the fresh redraw's), which Rust then builds and runs.
# A frame is the index of the attempt that built it: 0 the frame, 1 its
# full redraw, 2 its fresh redraw. Every check result is free.

# the checks the first k attempts give, in order (at most three)
def screen_paint_checks(ok1: Bool, ok2: Bool, ok3: Bool, k: Nat) -> List<&2, Bool>:
  List.take(&2, Bool, [ok1, ok2, ok3], k)

# whether the paint still needs a check after ks: every check run so far
# failed and fewer than n of them ran
def screen_paint_open.go(n: Nat, ks: List<&2, Bool>) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      match ks:
        case Nil{}:
          True{}
        case Con{ok, rest}:
          match ok:
            case True{}:
              False{}
            case False{}:
              screen_paint_open.go(m, rest)

def screen_paint_open(ks: List<&2, Bool>) -> Bool:
  screen_paint_open.go(3n, ks)

# what the entry answers: nothing yet while a check is still needed, else
# the paint
def screen_paint_step(open: Bool, p: Sc.Paint) -> Maybe<&2, Sc.Paint>:
  match open:
    case True{}:
      None{}
    case False{}:
      Some{p}

# LAW screen_ffi_paint: after any number of checks, the entry asks for the next check
# exactly while every check run so far failed (and fewer than three ran),
# and otherwise answers the paint of the first passing check
# (screen_paint_spec, the spec of paint_first_passing_check), whatever
# the checks not yet run would answer
# EXCLUDES: a paint decided before the check it depends on ran; a check
# asked for after the paint is settled (a redraw built for nothing); a
# frame drawn after its check failed; a passing redraw left unused; an
# outcome other than Kept after three failed checks; a wrong frame index
law screen_ffi_paint:
  for +k: Nat
  for +ok1: Bool
  for +ok2: Bool
  for +ok3: Bool
  {FSc.ffi(FSc.put_req(FSc.ReqPaint{screen_paint_checks(ok1, ok2, ok3, k)}, "")) == FSc.put_step(screen_paint_step(screen_paint_open(screen_paint_checks(ok1, ok2, ok3, k)), screen_paint_spec(0n, 1n, 2n, ok1, ok2, ok3)), "") : String}

# LAW screen_ffi_paint_example: the paint requests Rust writes, as text, with their replies; more
# than three checks is refused
# EXCLUDES: a request or reply format other than WIRE.md's (Bools as T
# and F with no comma, the step tags); a reply to a fourth check
law screen_ffi_paint_example:
  {[FSc.ffi("3,1,T"), FSc.ffi("3,1,F"), FSc.ffi("3,2,FT"), FSc.ffi("3,3,FFT"), FSc.ffi("3,3,FFF"), FSc.ffi("3,4,FFFF")] == ["1,0,F", "0,", "1,1,T", "2,2,", "3,0,", Wr.err("screen: more than three checks")] : List<&2, String>}

# ---- screen: the entry from the requirement ----

# The spec of the whole entry, written from the requirement (S8, the rules
# of the interface in the header of bend/screen.bend and the laws above)
# and the wire's primitives only: no function of bend/screen.bend or
# bend/ffi_screen.bend (their types only), but Sc.reveal through the plain
# formula pace_reveal_formula pins.

# block i (state s, length l) after the change g: Some{n} grows an active
# block by n characters, up to 2^32 - 1 (a length already past it stays),
# None makes it final; a final or committed block stays as it is
def sc_sp_change(g: Maybe<&2, Nat>, i: Nat, s: Sc.St, +l: Nat) -> Sc.Blk:
  match g:
    case None{}:
      match s:
        case Sc.Active{}:
          Sc.Blk{i, Sc.Final{}, l}
        case Sc.Final{}:
          Sc.Blk{i, Sc.Final{}, l}
        case Sc.Comm{}:
          Sc.Blk{i, Sc.Comm{}, l}
    case Some{n}:
      match s:
        case Sc.Active{}:
          Sc.Blk{i, Sc.Active{}, Nat.max(l, Nat.min(Nat.add(l, n), 4294967295n))}
        case Sc.Final{}:
          Sc.Blk{i, Sc.Final{}, l}
        case Sc.Comm{}:
          Sc.Blk{i, Sc.Comm{}, l}

# the block, changed by g when its id is the event's (hit)
def sc_sp_edit.at(hit: Bool, g: Maybe<&2, Nat>, i: Nat, s: Sc.St, l: Nat) -> Sc.Blk:
  match hit:
    case True{}:
      sc_sp_change(g, i, s, l)
    case False{}:
      Sc.Blk{i, s, l}

# every block of bs with id x changed by g, the others as they are
def sc_sp_edit(bs: List<&2, Sc.Blk>, +x: Nat, +g: Maybe<&2, Nat>) -> List<&2, Sc.Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      match b:
        case Sc.Blk{+i, s, l}:
          sc_sp_edit.at(Nat.is_eq(i, x), g, i, s, l) <> sc_sp_edit(rest, x, g)

# a flush: the final blocks from the start are committed, up to the first
# active block (it and every block after it stay)
def sc_sp_flush(bs: List<&2, Sc.Blk>) -> List<&2, Sc.Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              Sc.Blk{i, Sc.Comm{}, l} <> sc_sp_flush(rest)
            case Sc.Final{}:
              Sc.Blk{i, Sc.Comm{}, l} <> sc_sp_flush(rest)
            case Sc.Active{}:
              Sc.Blk{i, Sc.Active{}, l} <> rest

# one event on the transcript: Open adds an active empty block with the
# next id (then the next id is one more), Grow and Fin change the blocks
# with their id, Flush commits, Resize sets the width
def sc_sp_step(t: Sc.Tx, e: Sc.Ev) -> Sc.Tx:
  match t:
    case Sc.Tx{bs, +n, w}:
      match e:
        case Sc.Open{}:
          Sc.Tx{List.append(&2, Sc.Blk, bs, [Sc.Blk{n, Sc.Active{}, 0n}]), 1n+n, w}
        case Sc.Grow{x, k}:
          Sc.Tx{sc_sp_edit(bs, x, Some{k}), n, w}
        case Sc.Fin{x}:
          Sc.Tx{sc_sp_edit(bs, x, None{}), n, w}
        case Sc.Flush{}:
          Sc.Tx{sc_sp_flush(bs), n, w}
        case Sc.Resize{v}:
          Sc.Tx{bs, n, v}

# the events es, in order, on the transcript t
def sc_sp_run(es: List<&2, Sc.Ev>, t: Sc.Tx) -> Sc.Tx:
  match es:
    case Nil{}:
      t
    case e <> rest:
      sc_sp_run(rest, sc_sp_step(t, e))

# the characters a frame adds with backlog b (pace_reveal_formula)
def sc_sp_reveal(+min: Nat, +k: Nat, +b: Nat) -> Nat:
  Nat.min(b, Nat.max(min, Nat.div(b, 1n+k)))

# n characters arrive on the pace (r received, s shown), then a frame
def sc_sp_pace(+min: Nat, +k: Nat, +r: Nat, +s: Nat, +n: Nat) -> String:
  +r2 = Nat.add(r, n)
  Wr.put_nat(r2, Wr.put_nat(Nat.add(s, sc_sp_reveal(min, k, Nat.sub(r2, s))), ""))

# children of heights hs from row y in a viewport of `rows` rows: each at
# its row, its visible height cut at the viewport's bottom
def sc_sp_stack(hs: List<&2, Nat>, +y: Nat, +rows: Nat) -> List<&2, Sc.Rect>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> rest:
      Sc.Rect{y, Nat.min(h, Nat.sub(rows, y))} <> sc_sp_stack(rest, Nat.add(y, h), rows)

# the paint m when at most n more checks than the one it reads ran (r the
# checks after it), else none (more than three checks)
def sc_sp_short(r: List<&2, Bool>, n: Nat, m: Maybe<&2, Sc.Paint>) -> Maybe<&2, Sc.Paint>:
  match r:
    case Nil{}:
      m
    case x <> rest:
      match n:
        case 0n:
          None{}
        case 1n+k:
          sc_sp_short(rest, k, m)

# the third check c passed (the fresh redraw is drawn) or failed (the
# first frame is kept); r the checks after it
def sc_sp_d3(c: Bool, r: List<&2, Bool>) -> Maybe<&2, Sc.Paint>:
  match c:
    case True{}:
      sc_sp_short(r, 0n, Some{Sc.Fresh{2n}})
    case False{}:
      sc_sp_short(r, 0n, Some{Sc.Kept{0n}})

# the second check b passed (the full redraw is drawn), or the third
# decides
def sc_sp_d2(b: Bool, r: List<&2, Bool>) -> Maybe<&2, Sc.Paint>:
  match b:
    case True{}:
      sc_sp_short(r, 1n, Some{Sc.Put{1n, True{}}})
    case False{}:
      match r:
        case Nil{}:
          None{}
        case c <> rest:
          sc_sp_d3(c, rest)

# the first check a passed (the frame is drawn), or the second decides
def sc_sp_d1(a: Bool, r: List<&2, Bool>) -> Maybe<&2, Sc.Paint>:
  match a:
    case True{}:
      sc_sp_short(r, 2n, Some{Sc.Put{0n, False{}}})
    case False{}:
      match r:
        case Nil{}:
          None{}
        case b <> rest:
          sc_sp_d2(b, rest)

# the paint on the checks run so far, in order (the frame, its full
# redraw, its fresh redraw): the first passing check's frame; all three
# failed: kept, the first frame; while every check so far failed and
# fewer than three ran (or more than three ran): none yet
def sc_sp_decide(ks: List<&2, Bool>) -> Maybe<&2, Sc.Paint>:
  match ks:
    case Nil{}:
      None{}
    case a <> rest:
      sc_sp_d1(a, rest)

def sc_sp_put_st(s: Sc.St, rest: String) -> String:
  match s:
    case Sc.Active{}:
      Wr.put_nat(0n, rest)
    case Sc.Final{}:
      Wr.put_nat(1n, rest)
    case Sc.Comm{}:
      Wr.put_nat(2n, rest)

# a block: its id, its state's tag, its length
def sc_sp_put_blk(b: Sc.Blk, rest: String) -> String:
  match b:
    case Sc.Blk{i, s, l}:
      Wr.put_nat(i, sc_sp_put_st(s, Wr.put_nat(l, rest)))

# a transcript: its blocks, the next id, the width
def sc_sp_put_tx(t: Sc.Tx) -> String:
  match t:
    case Sc.Tx{bs, n, w}:
      Wr.put_list(~Sc.Blk, ~sc_sp_put_blk, bs, Wr.put_nat(n, Wr.put_nat(w, "")))

def sc_sp_put_rect(r: Sc.Rect, rest: String) -> String:
  match r:
    case Sc.Rect{y, h}:
      Wr.put_nat(y, Wr.put_nat(h, rest))

# a step of the paint: 0 (run the next check), 1 frame full, 2 frame, 3
# frame
def sc_sp_put_step(m: Maybe<&2, Sc.Paint>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{p}:
      match p:
        case Sc.Put{f, full}:
          Wr.put_nat(1n, Wr.put_nat(f, Wr.put_bool(full, "")))
        case Sc.Fresh{f}:
          Wr.put_nat(2n, Wr.put_nat(f, ""))
        case Sc.Kept{f}:
          Wr.put_nat(3n, Wr.put_nat(f, ""))

def sc_sp_paint.fit(fits: Bool, ks: List<&2, Bool>) -> String:
  match fits:
    case True{}:
      sc_sp_put_step(sc_sp_decide(ks))
    case False{}:
      Wr.err("screen: more than three checks")

# the reply to the checks run so far: more than three is an error
def sc_sp_paint(+ks: List<&2, Bool>) -> String:
  sc_sp_paint.fit(Nat.is_le(List.length(&2, Bool, ks), 3n), ks)

# the spec's answer to a request
def sc_sp_answer(q: FSc.Req) -> String:
  match q:
    case FSc.ReqRun{t, es}:
      sc_sp_put_tx(sc_sp_run(es, t))
    case FSc.ReqPace{min, k, p, n}:
      match p:
        case Sc.Pace{r, s}:
          sc_sp_pace(min, k, r, s, n)
    case FSc.ReqStack{hs, y, rows}:
      Wr.put_list(~Sc.Rect, ~sc_sp_put_rect, sc_sp_stack(hs, y, rows), "")
    case FSc.ReqPaint{ks}:
      sc_sp_paint(ks)

# The reader
# ----------

def sc_sp_st.tag(n: Nat, s: String) -> Wr.Dec<Sc.St>:
  match n:
    case 0n:
      Wr.Got{Sc.Active{}, s}
    case 1n:
      Wr.Got{Sc.Final{}, s}
    case 2n:
      Wr.Got{Sc.Comm{}, s}
    case 3n+p:
      Wr.Bad{}

def sc_sp_st.of(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.St>:
  match r:
    case Wr.Got{n, s}:
      sc_sp_st.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_blk.len(i: Nat, st: Sc.St, r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Blk>:
  match r:
    case Wr.Got{l, s}:
      Wr.Got{Sc.Blk{i, st, l}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_blk.st(i: Nat, r: Wr.Dec<Sc.St>) -> Wr.Dec<Sc.Blk>:
  match r:
    case Wr.Got{st, s}:
      sc_sp_blk.len(i, st, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_blk.id(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Blk>:
  match r:
    case Wr.Got{i, s}:
      sc_sp_blk.st(i, sc_sp_st.of(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# a block: its id, its state's tag (0 active, 1 final, 2 committed), its
# length
def sc_sp_blk(s: String) -> Wr.Dec<Sc.Blk>:
  sc_sp_blk.id(Wr.get_nat(s))

def sc_sp_ev.one(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Ev>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Sc.Fin{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_ev.w(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Ev>:
  match r:
    case Wr.Got{w, s}:
      Wr.Got{Sc.Resize{w}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_ev.n(x: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Ev>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Sc.Grow{x, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_ev.x(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Ev>:
  match r:
    case Wr.Got{x, s}:
      sc_sp_ev.n(x, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_ev.tag(n: Nat, s: String) -> Wr.Dec<Sc.Ev>:
  match n:
    case 0n:
      Wr.Got{Sc.Open{}, s}
    case 1n:
      sc_sp_ev.x(Wr.get_nat(s))
    case 2n:
      sc_sp_ev.one(Wr.get_nat(s))
    case 3n:
      Wr.Got{Sc.Flush{}, s}
    case 4n:
      sc_sp_ev.w(Wr.get_nat(s))
    case 5n+p:
      Wr.Bad{}

def sc_sp_ev.of(r: Wr.Dec<Nat>) -> Wr.Dec<Sc.Ev>:
  match r:
    case Wr.Got{n, s}:
      sc_sp_ev.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

# an event: its tag (0 Open, 1 Grow, 2 Fin, 3 Flush, 4 Resize), then its
# fields
def sc_sp_ev(s: String) -> Wr.Dec<Sc.Ev>:
  sc_sp_ev.of(Wr.get_nat(s))

def sc_sp_run.es(t: Sc.Tx, r: Wr.Dec<List<&2, Sc.Ev>>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{es, s}:
      Wr.Got{FSc.ReqRun{t, es}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_run.w(bs: List<&2, Sc.Blk>, n: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{w, s}:
      sc_sp_run.es(Sc.Tx{bs, n, w}, Wr.get_list(~Sc.Ev, ~sc_sp_ev, s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_run.n(bs: List<&2, Sc.Blk>, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{n, s}:
      sc_sp_run.w(bs, n, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a run: the blocks, the next id, the width, then the events
def sc_sp_run.bs(r: Wr.Dec<List<&2, Sc.Blk>>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{bs, s}:
      sc_sp_run.n(bs, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_pacereq.n(min: Nat, k: Nat, rv: Nat, sh: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{FSc.ReqPace{min, k, Sc.Pace{rv, sh}, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_pacereq.sh(min: Nat, k: Nat, rv: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{sh, s}:
      sc_sp_pacereq.n(min, k, rv, sh, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_pacereq.rv(min: Nat, k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{rv, s}:
      sc_sp_pacereq.sh(min, k, rv, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_pacereq.k(min: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{k, s}:
      sc_sp_pacereq.rv(min, k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a pace: the minimum, the lag, received, shown, then the characters
# that arrive
def sc_sp_pacereq(r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{min, s}:
      sc_sp_pacereq.k(min, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_stack.rows(hs: List<&2, Nat>, y: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{rows, s}:
      Wr.Got{FSc.ReqStack{hs, y, rows}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_stack.y(hs: List<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{y, s}:
      sc_sp_stack.rows(hs, y, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a stack: the heights, the start row, the rows
def sc_sp_stack.hs(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{hs, s}:
      sc_sp_stack.y(hs, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a paint: the checks run so far
def sc_sp_paintreq(r: Wr.Dec<List<&2, Bool>>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{ks, s}:
      Wr.Got{FSc.ReqPaint{ks}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sc_sp_req.tag(n: Nat, s: String) -> Wr.Dec<FSc.Req>:
  match n:
    case 0n:
      sc_sp_run.bs(Wr.get_list(~Sc.Blk, ~sc_sp_blk, s))
    case 1n:
      sc_sp_pacereq(Wr.get_nat(s))
    case 2n:
      sc_sp_stack.hs(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 3n:
      sc_sp_paintreq(Wr.get_list(~Bool, ~Wr.get_bool, s))
    case 4n+p:
      Wr.Bad{}

def sc_sp_req.of(r: Wr.Dec<Nat>) -> Wr.Dec<FSc.Req>:
  match r:
    case Wr.Got{n, s}:
      sc_sp_req.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with: its tag (0 run, 1 pace, 2 stack, 3 paint),
# then its fields; and what follows
def sc_sp_req(s: String) -> Wr.Dec<FSc.Req>:
  sc_sp_req.of(Wr.get_nat(s))

def sc_sp.whole(q: FSc.Req, whole: Bool) -> String:
  match whole:
    case True{}:
      sc_sp_answer(q)
    case False{}:
      Wr.err("screen: input left over")

def sc_sp.of(r: Wr.Dec<FSc.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      sc_sp.whole(q, Wr.end(s))
    case Wr.Bad{}:
      Wr.err("screen: malformed request")

# the entry's answer to the input s
def sc_spec(s: String) -> String:
  sc_sp.of(sc_sp_req(s))

# LAW screen_ffi_exact (compiled core): on every input the interface's
# entry answers the spec: for a run the transcript after the frame's
# events (Open adds an active empty block with the next id; Grow lengthens
# each active block of its id, up to 2^32 - 1 characters; Fin makes
# each active block of its id final; Flush commits the final blocks from
# the start up to the first active one; Resize sets the width); for a pace
# the characters received and those a frame shows (the plain formula of
# pace_reveal_formula); for a stack each child's row and visible height;
# for a paint the first passing check's frame, Kept after three failed,
# else a request for the next check; and exactly "screen: more than three
# checks", "screen: input left over" or "screen: malformed request"
# otherwise
# EXCLUDES: a block changed by an event of another id, a committed block
#   changed, a flush past an active block, an Open with another id, a
#   pace or a stack by another rule, a paint before its check, a field
#   misread, a reply spelled otherwise, a default for malformed input,
#   input left over ignored, another error text
law screen_ffi_exact:
  for +s: String
  {FSc.ffi(s) == sc_spec(s) : String}

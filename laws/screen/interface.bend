# eukhe: the laws of area screen, section interface: the interface (S8) and the entry
# bend/ffi_screen.bend by its wire and by the grammar's spelling. The other sections:
# laws/screen/events.bend (each event of the transcript) and laws/screen/recover.bend
# (the recoveries of H4.8, bend/run/recovery.bend)

import Base
import ../../bend/ffi_screen.bend as FSc
import ../../bend/screen.bend as Sc
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# Requirements (S8, the header of bend/screen.bend; the entry: crates/eukhe-tui
# view/ledger.rs, pace.rs, view/stack.rs, inline_term.rs). Each with the laws
# that state it.
# R1  Open starts a block, active and empty, with the next id; the blocks
#     stay in the order they opened: tx_ids_count_opens, tx_open_appends_fresh
#     (events.bend)
# R2  Grow{x, n}: each active block of id x gets n more characters, up to
#     2^32 - 1 (a length already past it stays); a final or committed
#     block's text is fixed; no other block changes: tx_grow_lengthens
#     (events.bend)
# R3  Fin{x}: each active block of id x is final; no other change:
#     tx_fin_finishes (events.bend)
# R4  Flush commits the final blocks in order, up to the first active one:
#     tx_flush_settles, tx_flush_only_commits (events.bend), tx_gapless
# R5  Committed text is never written again: the scrollback only grows, and
#     the width (a resize) changes no block: tx_scrollback_append_only,
#     tx_gapless, tx_width_never_matters
# R6  Committed blocks are inert, so the core runs a frame on the blocks
#     after the committed prefix alone: tx_committed_inert (anchors
#     all_comm_example, all_comm_rejects_example)
# R7  Pacing: a frame shows at least `min` characters of the backlog b and
#     the share b / (1 + k) when that is more, never more than arrived,
#     never less than before, all of it within b frames: pace_never_ahead,
#     pace_never_back, pace_drains, pace_reveal_formula
# R8  Off-screen verification: the first of the three checks (the frame,
#     its full redraw, its fresh redraw) that passes picks what reaches the
#     terminal; all three failed: nothing drawn, the frame kept:
#     verify_only_checked, paint_picks_first_pass
# R9  Layout: children one under the other from the start row, each cut at
#     the viewport's bottom: layout_inside, layout_apart,
#     layout_whole_when_room, layout_child_at
# R10 The entry answers each request Rust spells (WIRE.md's grammar) with
#     the model's decision in the grammar Rust reads, and the error form for
#     any other input: screen_ffi_answers_spelled,
#     screen_ffi_left_over_spelled, screen_ffi_unknown_request,
#     screen_ffi_unknown_state, screen_ffi_unknown_event,
#     screen_ffi_reads_only_requests, screen_ffi_malformed_unless_request,
#     screen_ffi_run (anchors screen_ffi_example, screen_ffi_refuses_example,
#     screen_ffi_tags_example)
# A1  The paint decision asks for the next check exactly while it is still
#     needed (inline_term.rs `paint_decision` builds a redraw only when
#     asked): screen_ffi_paint (anchor screen_ffi_paint_example)
# A2  (H4.8 of laws/run/model.bend) a recovery's cap counts only its own
#     notes in a row: rec_length_notes_then_quit, rec_leak_notes_then_quit
#     (recover.bend: the model's rows from any row); a row that restarts
#     after another recovery's note: rec_length_notes_then_fails,
#     rec_leak_notes_then_fails (laws/run/recover.bend, on decide.recover)

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

# the events es with every resize left out
def tx_no_resize(es: List<&2, Sc.Ev>) -> List<&2, Sc.Ev>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Sc.Open{}:
          Sc.Open{} <> tx_no_resize(rest)
        case Sc.Grow{x, k}:
          Sc.Grow{x, k} <> tx_no_resize(rest)
        case Sc.Fin{x}:
          Sc.Fin{x} <> tx_no_resize(rest)
        case Sc.Flush{}:
          Sc.Flush{} <> tx_no_resize(rest)
        case Sc.Resize{v}:
          tx_no_resize(rest)

# LAW tx_width_never_matters (R5): the width never touches a block: any events
# on any blocks and next id, under any width, leave the blocks the same events
# without their resizes leave under any other width. So a resize writes no
# block again, and no event reads the width
# EXCLUDES: a resize that rewrites, reflows, drops or commits a block (the
#   scrollback written again), an event whose effect on a block depends on
#   the width
law tx_width_never_matters:
  for es: List<&2, Sc.Ev>
  for +bs: List<&2, Sc.Blk>
  for +n: Nat
  for w: Nat
  for v: Nat
  {Sc.Tx.blocks(Sc.run(es, Sc.Tx{bs, n, w})) == Sc.Tx.blocks(Sc.run(tx_no_resize(es), Sc.Tx{bs, n, v})) : List<&2, Sc.Blk>}

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

# LAW verify_only_checked (R8): present's outcome agrees with the two checks: a
# diff draw only when the first check passed, a full redraw only when the
# second passed, the error only when both failed. Which frame is drawn, and
# that a passing first check wins, are paint_picks_first_pass's
law verify_only_checked:
  for f: Nat
  for g: Nat
  for +ok1: Bool
  for +ok2: Bool
  {Sc.checked(Sc.present(f, g, ok1, ok2), ok1, ok2) == True{} : Bool}

# the paint the entry laws below expect (screen_ffi_paint,
# screen_ffi_answers_spelled): the first of the three checks that passes
# picks the frame drawn (the frame f, its full redraw g, its fresh redraw h
# on a blank screen); when none passes nothing is drawn and the first frame
# is kept
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

# p is the paint of the first passing check: the frame f as a diff when the
# first check passed; its full redraw g when the second passed and the first
# failed; its fresh redraw h when the third passed and both before failed;
# f kept when all three failed. For given checks exactly one paint holds it
def paint_first_pass(+f: Nat, +g: Nat, +h: Nat, +ok1: Bool, +ok2: Bool, +ok3: Bool, p: Sc.Paint) -> Bool:
  match p:
    case Sc.Put{x, full}:
      match full:
        case False{}:
          Bool.and(Nat.is_eq(x, f), ok1)
        case True{}:
          Bool.and(Nat.is_eq(x, g), Bool.and(Bool.not(ok1), ok2))
    case Sc.Fresh{x}:
      Bool.and(Nat.is_eq(x, h), Bool.and(Bool.not(ok1), Bool.and(Bool.not(ok2), ok3)))
    case Sc.Kept{x}:
      Bool.and(Nat.is_eq(x, f), Bool.and(Bool.not(ok1), Bool.and(Bool.not(ok2), Bool.not(ok3))))

# LAW paint_picks_first_pass (R8): for any frames and check results, what
# present then resync send to the terminal is the paint of the first passing
# check (paint_first_pass: the frame, its full redraw, its fresh redraw on a
# blank screen, each only when its check passed and every check before it
# failed); all three failed: nothing drawn, the first frame kept, the
# surface goes on. Exactly one paint satisfies paint_first_pass, so this
# pins present and resync
# EXCLUDES: a frame drawn after its check failed; a frame drawn other than
#   the one whose check passed; a passing redraw left unused; a full or
#   fresh redraw before the checks before it failed; any outcome but Kept
#   of the first frame after three failed checks
law paint_picks_first_pass:
  for +f: Nat
  for +g: Nat
  for +h: Nat
  for +ok1: Bool
  for +ok2: Bool
  for +ok3: Bool
  {paint_first_pass(f, g, h, ok1, ok2, ok3, Sc.resync(Sc.present(f, g, ok1, ok2), h, ok3)) == True{} : Bool}

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

# the i-th rect of rs (from 0), none past the end
def layout_rect_at(rs: List<&2, Sc.Rect>, i: Nat) -> Maybe<&2, Sc.Rect>:
  match rs:
    case Nil{}:
      None{}
    case r <> rest:
      match i:
        case 0n:
          Some{r}
        case 1n+j:
          layout_rect_at(rest, j)

# the i-th height of hs (from 0), none past the end
def layout_height_at(hs: List<&2, Nat>, i: Nat) -> Maybe<&2, Nat>:
  match hs:
    case Nil{}:
      None{}
    case h <> rest:
      match i:
        case 0n:
          Some{h}
        case 1n+j:
          layout_height_at(rest, j)

# the rows the first i children of heights hs take, whole
def layout_above(hs: List<&2, Nat>, i: Nat) -> Nat:
  match hs:
    case Nil{}:
      0n
    case h <> rest:
      match i:
        case 0n:
          0n
        case 1n+j:
          Nat.add(h, layout_above(rest, j))

# a child of height m placed at row top of a viewport of `rows` rows: its
# rows from top down to the viewport's bottom at most
def layout_place(m: Maybe<&2, Nat>, +top: Nat, +rows: Nat) -> Maybe<&2, Sc.Rect>:
  match m:
    case None{}:
      None{}
    case Some{h}:
      Some{Sc.Rect{top, Nat.min(h, Nat.sub(rows, top))}}

# LAW layout_child_at (R9): for any heights, start row, rows and index i,
# the i-th rect of the stack is the i-th child placed at the start row plus
# the whole heights of the children before it, its visible height cut at
# the viewport's bottom; past the last child there is no rect (one rect per
# child)
# EXCLUDES: a gap or an overlap between children, a child placed after the
#   visible part of the one before (a clipped child's hidden rows dropped),
#   a partly visible child shown whole or hidden, a rect dropped or added,
#   children reordered
law layout_child_at:
  for +hs: List<&2, Nat>
  for +y: Nat
  for +rows: Nat
  for +i: Nat
  {layout_rect_at(Sc.vstack(hs, y, rows), i) == layout_place(layout_height_at(hs, i), Nat.add(layout_above(hs, i), y), rows) : Maybe<&2, Sc.Rect>}

# LAW pace_reveal_formula: the guarded share is the plain formula, for every minimum, lag and
# backlog: a frame reveals min(b, max(min, b / (1 + k)))
# EXCLUDES: a guard (no 1 + k formed when k >= b) that changes the
# reveal for some lag
law pace_reveal_formula:
  for +min: Nat
  for +k: Nat
  for +b: Nat
  {Sc.reveal(min, k, b) == Nat.min(b, Nat.max(min, Nat.div(b, 1n+k))) : Nat}

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

# LAW all_comm_rejects_example: anchor: a prefix with a final or an active block is not committed
# EXCLUDES: an all_comm that is always True
law all_comm_rejects_example:
  {Bool.or(all_comm([Sc.Blk{0n, Sc.Final{}, 0n}]), all_comm([Sc.Blk{0n, Sc.Comm{}, 0n}, Sc.Blk{1n, Sc.Active{}, 0n}])) == False{} : Bool}

# ---- screen: the entry ----

# LAWS (S8, the compiled core): the interface's rules run as the model of
# bend/screen.bend through the compiled core's entry bend/ffi_screen.bend
# (crates/eukhe-tui: view/ledger.rs, pace.rs, view/stack.rs). The laws of
# the model itself are in the first section, (S8) The interface. Every
# input is free: any transcript, events, pace, rate and heights whose
# numbers fit the wire.

# The compiled core's entry of the interface (bend/ffi_screen.bend): Rust
# writes a request in WIRE.md's grammar (spelled below from the wire
# primitives, screen_spell_req) and reads the reply; FSc.put_req is the
# entry's own encoder of a request. Every Nat of a request fits the wire
# (at most 14 digits, wire_fits)

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

# LAW screen_ffi_run (R10): a Run request written by the entry's own encoder
# (FSc.put_req), every number within the wire, is answered with the
# transcript Sc.run gives on its events, written by the entry's own encoder
# (FSc.put_tx): the entry's decoder reads back what its encoder writes, and
# it runs the events it read. A tag or field order shared wrong by the
# entry's encoders and decoders passes it; that the codec is the grammar
# Rust writes and reads is screen_ffi_answers_spelled's
# EXCLUDES: an entry that drops, invents or reorders the events or blocks
#   it reads back, or answers another transcript than Sc.run's
law screen_ffi_run:
  for +t: Sc.Tx
  for +es: List<&2, Sc.Ev>
  for +ft: {tx_fits(t) == True{} : Bool}
  for +fe: {Bool.and(LawsBase.wire_fits(List.length(&2, Sc.Ev, es)), evs_fit(es)) == True{} : Bool}
  {FSc.ffi(FSc.put_req(FSc.ReqRun{t, es}, "")) == FSc.put_tx(Sc.run(es, t), "") : String}

# LAW screen_ffi_example: anchor: three requests spelled by hand from WIRE.md's grammar
# and the request layout (no Rust test holds these bytes): a frame (blocks
# 5 and 6 live, open one, finish 5, flush), a pace frame and a stack, with
# their replies
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
# (screen_paint_spec: the first passing check's paint, which
# paint_picks_first_pass pins for the model's present and resync), whatever
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

# LAW screen_ffi_paint_example: anchor: paint requests spelled by hand from WIRE.md's
# grammar (no Rust test holds these bytes), with their replies; more than
# three checks is refused
# EXCLUDES: a request or reply format other than WIRE.md's (Bools as T
# and F with no comma, the step tags); a reply to a fourth check
law screen_ffi_paint_example:
  {[FSc.ffi("3,1,T"), FSc.ffi("3,1,F"), FSc.ffi("3,2,FT"), FSc.ffi("3,3,FFT"), FSc.ffi("3,3,FFF"), FSc.ffi("3,4,FFFF")] == ["1,0,F", "0,", "1,1,T", "2,2,", "3,0,", Wr.err("screen: more than three checks")] : List<&2, String>}

# The screen entry, spelled by the grammar Rust writes and reads
# (crates/eukhe-tui: view/ledger.rs `write_run`/`read_run`, pace.rs
# `frame`, view/stack.rs `stack_rows`, inline_term.rs `paint_decision`),
# from the wire primitives only, never the entry's own encoders. Each
# constructor is its tag, then its fields in order; a list is its count,
# then its items.

# a block state: Active 0, Final 1, Committed 2
def screen_spell_st(s: Sc.St, rest: String) -> String:
  match s:
    case Sc.Active{}:
      Wr.put_nat(0n, rest)
    case Sc.Final{}:
      Wr.put_nat(1n, rest)
    case Sc.Comm{}:
      Wr.put_nat(2n, rest)

# a block: its id, its state, its length
def screen_spell_blk(b: Sc.Blk, rest: String) -> String:
  match b:
    case Sc.Blk{i, s, l}:
      Wr.put_nat(i, screen_spell_st(s, Wr.put_nat(l, rest)))

# the blocks of bs, each spelled, then rest
def screen_spell_blks.items(bs: List<&2, Sc.Blk>, rest: String) -> String:
  match bs:
    case Nil{}:
      rest
    case Con{b, t}:
      screen_spell_blk(b, screen_spell_blks.items(t, rest))

# a list of blocks: its count, then each block
def screen_spell_blks(+bs: List<&2, Sc.Blk>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Sc.Blk, bs), screen_spell_blks.items(bs, rest))

# a transcript: its blocks, the next id, the width
def screen_spell_tx(t: Sc.Tx, rest: String) -> String:
  match t:
    case Sc.Tx{bs, n, w}:
      screen_spell_blks(bs, Wr.put_nat(n, Wr.put_nat(w, rest)))

# an event: Open 0; Grow 1, the id, the growth; Fin 2, the id; Flush 3;
# Resize 4, the width
def screen_spell_ev(e: Sc.Ev, rest: String) -> String:
  match e:
    case Sc.Open{}:
      Wr.put_nat(0n, rest)
    case Sc.Grow{x, n}:
      Wr.put_nat(1n, Wr.put_nat(x, Wr.put_nat(n, rest)))
    case Sc.Fin{x}:
      Wr.put_nat(2n, Wr.put_nat(x, rest))
    case Sc.Flush{}:
      Wr.put_nat(3n, rest)
    case Sc.Resize{w}:
      Wr.put_nat(4n, Wr.put_nat(w, rest))

# the events of es, each spelled, then rest
def screen_spell_evs.items(es: List<&2, Sc.Ev>, rest: String) -> String:
  match es:
    case Nil{}:
      rest
    case Con{e, t}:
      screen_spell_ev(e, screen_spell_evs.items(t, rest))

# a list of events: its count, then each event
def screen_spell_evs(+es: List<&2, Sc.Ev>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Sc.Ev, es), screen_spell_evs.items(es, rest))

# the check results of ks, each T or F, then rest
def screen_spell_bools.items(ks: List<&2, Bool>, rest: String) -> String:
  match ks:
    case Nil{}:
      rest
    case Con{k, t}:
      Wr.put_bool(k, screen_spell_bools.items(t, rest))

# a list of check results: its count, then each result
def screen_spell_bools(+ks: List<&2, Bool>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Bool, ks), screen_spell_bools.items(ks, rest))

# a pace: the characters received, then those shown
def screen_spell_pace(p: Sc.Pace, rest: String) -> String:
  match p:
    case Sc.Pace{r, s}:
      Wr.put_nat(r, Wr.put_nat(s, rest))

# a rect: its first row, its height
def screen_spell_rect(r: Sc.Rect, rest: String) -> String:
  match r:
    case Sc.Rect{y, h}:
      Wr.put_nat(y, Wr.put_nat(h, rest))

# the rects of rs, each spelled, then rest
def screen_spell_rects.items(rs: List<&2, Sc.Rect>, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case Con{r, t}:
      screen_spell_rect(r, screen_spell_rects.items(t, rest))

# a list of rects: its count, then each rect
def screen_spell_rects(+rs: List<&2, Sc.Rect>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Sc.Rect, rs), screen_spell_rects.items(rs, rest))

# a request: 0 Run (the transcript, the events); 1 Pace (the minimum, the
# lag, the pace, the characters that arrive); 2 Stack (the heights, the
# first row, the rows); 3 Paint (the checks run so far)
def screen_spell_req(q: FSc.Req, rest: String) -> String:
  match q:
    case FSc.ReqRun{t, es}:
      Wr.put_nat(0n, screen_spell_tx(t, screen_spell_evs(es, rest)))
    case FSc.ReqPace{min, k, p, n}:
      Wr.put_nat(1n, Wr.put_nat(min, Wr.put_nat(k, screen_spell_pace(p, Wr.put_nat(n, rest)))))
    case FSc.ReqStack{hs, y, rows}:
      Wr.put_nat(2n, LawsBase.wire_spell_nats(hs, Wr.put_nat(y, Wr.put_nat(rows, rest))))
    case FSc.ReqPaint{ks}:
      Wr.put_nat(3n, screen_spell_bools(ks, rest))

# every Nat of a pace fits the wire
def screen_pace_fits(p: Sc.Pace) -> Bool:
  match p:
    case Sc.Pace{r, s}:
      Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(s))

# every Nat of a request fits the wire, every list count too
def screen_req_fits(q: FSc.Req) -> Bool:
  match q:
    case FSc.ReqRun{t, +es}:
      Bool.and(tx_fits(t), Bool.and(LawsBase.wire_fits(List.length(&2, Sc.Ev, es)), evs_fit(es)))
    case FSc.ReqPace{min, k, p, n}:
      Bool.and(Bool.and(LawsBase.wire_fits(min), LawsBase.wire_fits(k)), Bool.and(screen_pace_fits(p), LawsBase.wire_fits(n)))
    case FSc.ReqStack{+hs, y, rows}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)), Bool.and(LawsBase.wire_fits(y), LawsBase.wire_fits(rows)))
    case FSc.ReqPaint{ks}:
      LawsBase.wire_fits(List.length(&2, Bool, ks))

# a paint step: 0 run the next check; 1 the frame drawn, then T for a full
# redraw (F: a diff); 2 the frame drawn fresh; 3 the frame kept
def screen_spell_step(m: Maybe<&2, Sc.Paint>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{p}:
      match p:
        case Sc.Put{f, full}:
          Wr.put_nat(1n, Wr.put_nat(f, Wr.put_bool(full, rest)))
        case Sc.Fresh{f}:
          Wr.put_nat(2n, Wr.put_nat(f, rest))
        case Sc.Kept{f}:
          Wr.put_nat(3n, Wr.put_nat(f, rest))

# the result of check i of ks (a check not yet run: False; the decision
# never depends on one)
def screen_paint_at(ks: List<&2, Bool>, i: Nat) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{k, rest}:
      match i:
        case 0n:
          k
        case 1n+j:
          screen_paint_at(rest, j)

# the reply to the checks ks when at most three ran (fits), else the error
# form "screen: more than three checks": the next check while it is still
# needed, else the paint of the first passing check (screen_paint_spec)
def screen_paint_reply.fit(fits: Bool, +ks: List<&2, Bool>) -> String:
  match fits:
    case True{}:
      screen_spell_step(screen_paint_step(screen_paint_open(ks), screen_paint_spec(0n, 1n, 2n, screen_paint_at(ks, 0n), screen_paint_at(ks, 1n), screen_paint_at(ks, 2n))), "")
    case False{}:
      Wr.err("screen: more than three checks")

def screen_paint_reply(+ks: List<&2, Bool>) -> String:
  screen_paint_reply.fit(Nat.is_le(List.length(&2, Bool, ks), 3n), ks)

# the spelled reply of the model's decision on request q: the transcript
# Sc.run gives; the pace after n characters and a frame; the rects of
# Sc.vstack; the paint step
def screen_spell_answer(q: FSc.Req) -> String:
  match q:
    case FSc.ReqRun{t, es}:
      screen_spell_tx(Sc.run(es, t), "")
    case FSc.ReqPace{min, k, p, n}:
      screen_spell_pace(Sc.pace.run([Sc.Chunk{n}, Sc.Frame{}], min, k, p), "")
    case FSc.ReqStack{hs, y, rows}:
      screen_spell_rects(Sc.vstack(hs, y, rows), "")
    case FSc.ReqPaint{ks}:
      screen_paint_reply(ks)

# LAW screen_ffi_answers_spelled: a request spelled by the grammar, every number and count
# within the wire, is answered with the grammar's spelling of the model's
# decision: a Run the transcript Sc.run gives (blocks with their state
# tags, next id, width); a Pace the pace after n characters and a frame
# (recv, then shown); a Stack the rects of Sc.vstack (count, then y and h
# each); a Paint of at most three checks the step (0 next check, 1 frame
# and T/F full, 2 fresh frame, 3 kept frame), of more the error form
# "screen: more than three checks"
# EXCLUDES: a request, state, event or step tag that drifts from the
#   grammar Rust reads and writes (swapped on both sides of the entry
#   alike), a field lost, swapped or defaulted, recv and shown or y and h
#   written in the other order, a reversed full flag, a paint decided on
#   other checks, a fourth check answered
law screen_ffi_answers_spelled:
  for +q: FSc.Req
  for fits: {screen_req_fits(q) == True{} : Bool}
  {FSc.ffi(screen_spell_req(q, "")) == screen_spell_answer(q) : String}

# LAW screen_ffi_left_over_spelled: a spelled request that fits, followed by any more input,
# answers the error form "screen: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request, or
#   answered with another error
law screen_ffi_left_over_spelled:
  for +q: FSc.Req
  for fits: {screen_req_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {FSc.ffi(screen_spell_req(q, SCon{c, t})) == Wr.err("screen: input left over") : String}

# LAW screen_ffi_unknown_request: a request tag of 4 or more (of any length) answers the error
# form "screen: malformed request", whatever follows
# EXCLUDES: an unknown request tag read as a known request, or as another
#   error
law screen_ffi_unknown_request:
  for +n: Nat
  for +rest: String
  {FSc.ffi(Wr.put_nat(4n+n, rest)) == Wr.err("screen: malformed request") : String}

# LAW screen_ffi_unknown_state: a Run whose first block (any count, any id) has a state tag
# of 3 or more answers the error form "screen: malformed request",
# whatever follows
# EXCLUDES: an unknown block state read as active, final or committed
law screen_ffi_unknown_state:
  for +m: Nat
  for +i: Nat
  for +n: Nat
  for +rest: String
  {FSc.ffi(Wr.put_nat(0n, Wr.put_nat(1n+m, Wr.put_nat(i, Wr.put_nat(3n+n, rest))))) == Wr.err("screen: malformed request") : String}

# LAW screen_ffi_unknown_event: a Run with a spelled transcript that fits, whose first event
# (any count) has a tag of 5 or more, answers the error form "screen:
# malformed request", whatever follows
# EXCLUDES: an unknown event read as a known event, or skipped
law screen_ffi_unknown_event:
  for +t: Sc.Tx
  for ft: {tx_fits(t) == True{} : Bool}
  for +m: Nat
  for +n: Nat
  for +rest: String
  {FSc.ffi(Wr.put_nat(0n, screen_spell_tx(t, Wr.put_nat(1n+m, Wr.put_nat(5n+n, rest))))) == Wr.err("screen: malformed request") : String}

# LAW screen_ffi_reads_only_requests: an answer that is not the error form answers a request:
# the input is exactly the spelling of a request whose numbers fit the
# wire, and the answer is the spelled reply of the model's decision on it
# EXCLUDES: a decoder that accepts an unknown tag (request, state, event),
#   a check that is not T or F, a missing or extra field or item, or input
#   left over, and answers it anyway (a default instead of the error form)
law screen_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSc.ffi(s)) == False{} : Bool}
  exs q: FSc.Req
  {(s, (screen_req_fits(q), FSc.ffi(s))) == (screen_spell_req(q, ""), (True{}, screen_spell_answer(q))) : String & (Bool & String)}

# LAW screen_ffi_malformed_unless_request: every answer but the error form "screen: malformed
# request" comes from an input that begins with a spelled request that fits
# (so, with screen_ffi_answers_spelled and screen_ffi_left_over_spelled,
# every input's answer is pinned)
# EXCLUDES: the left-over or the more-than-three error (or any answer) for
#   input that does not begin with a request, the malformed error spelled
#   with another text
law screen_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FSc.ffi(s), Wr.err("screen: malformed request")) == False{} : Bool}
  exs q: FSc.Req
  exs rest: String
  {(s, screen_req_fits(q)) == (screen_spell_req(q, rest), True{}) : String & Bool}

# LAW screen_ffi_tags_example: anchor: the bytes Rust sends and reads: a Run of block 5
# (final) and 6 (active) with Open, Grow 5 by 2 (a final block does not
# grow), Fin 6, Flush and Resize 9 (blocks 5 and 6 committed, both of
# length 0, 7 active, next 8, width 9); a
# Pace (min 1, lag 2, recv 5, shown 1, 3 arrive: recv 8, shown 3); a Stack
# (heights 1 and 3 from row 1 of 3: rects 1+1 and 2+1); Paint steps Put
# (frame 0, diff), next check, Fresh 2, Kept 0; request tag 4, state tag 3
# and event tag 5 are malformed; a Paint of four checks is refused; a
# request with input left over is refused. The Grow is of the final
# block: an active block's growth is capped at 2^32 - 1 (Sc.grow1), a
# literal the --verdict kernel runs out of fuel on in a closed evaluation
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, a reversed full flag, an unknown tag read as a known one
law screen_ffi_tags_example:
  {[FSc.ffi("0,2,5,1,0,6,0,0,7,4,5,0,1,5,2,2,6,3,4,9,"), FSc.ffi("1,1,2,5,1,3,"), FSc.ffi("2,2,1,3,1,3,"), FSc.ffi("3,1,T"), FSc.ffi("3,1,F"), FSc.ffi("3,3,FFT"), FSc.ffi("3,3,FFF"), FSc.ffi("4,"), FSc.ffi("0,1,0,3,0,0,0,0,"), FSc.ffi("0,0,0,0,1,5,"), FSc.ffi("3,4,FFFF"), FSc.ffi("1,1,2,5,1,3,x")] == ["3,5,2,0,6,2,0,7,0,0,8,9,", "8,3,", "2,1,1,2,1,", "1,0,F", "0,", "2,2,", "3,0,", Wr.err("screen: malformed request"), Wr.err("screen: malformed request"), Wr.err("screen: malformed request"), Wr.err("screen: more than three checks"), Wr.err("screen: input left over")] : List<&2, String>}

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

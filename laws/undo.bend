# eukhe: the laws of area undo
#
# The per-prompt workspace snapshots of a top-level session (bend/undo.bend),
# run as the compiled core by bend/ffi_undo.bend (eukhe-bend rules/undo.rs,
# called by crates/eukhe-core/src/undo for /undo and /diff). A history is
# the list of events a session saw, newest first; every history, state and
# row is free.
#
# R1: after any history, the snapshots not undone are the turns no later
#     /undo took back, newest first (each /undo takes back the newest turn
#     not yet taken back; a /undo with none left takes back nothing), and
#     the session's first snapshot is the oldest turn of the history, undone
#     or not. A turn after undos so stands on what is left: the undone
#     snapshots never come back.
# R2: /undo restores the newest snapshot not undone and drops it, from any
#     state Rust stored, whatever its first snapshot; with none left it is
#     refused. A turn start, from any state, only keeps its snapshot: no
#     snapshot is restored but by /undo. From any state Rust stored,
#     whatever its first snapshot, a turn start t puts t newest in front of
#     the snapshots left, dropping none, and keeps the first snapshot, or
#     makes t the first when none is recorded.
# R3: a refused /undo changes nothing.
# R4: /diff compares the workspace with the newest snapshot not undone
#     (the turn) or with the session's first snapshot (all), from any state
#     Rust stored, whatever its first snapshot; with no such snapshot there
#     is nothing to compare. /diff changes nothing.
# R5: /undo restores exactly the snapshot's content of every row that is
#     not held: a path added since is removed, a path removed or changed
#     since gets the snapshot's content back; a held row (ignored, over the
#     size cap, a nested repository) keeps the workspace's content.
# R6: /undo touches exactly the rows that are not held and whose content
#     differs: a held row, or one with the same content (paths in neither
#     side included), is left alone.
# R7: /diff lists exactly the rows that differ: a held row is skipped, a
#     row with the same content is the same, every other row differs.
# R8: the entry answers each request Rust writes (every number and count
#     within the wire) with the answer of R1-R7, reads exactly the request
#     and nothing after it, and answers any other input with the exact
#     error form `E undo: malformed request`.
#
# Not pinned here, gated by Rust tests: a turn whose snapshot failed is
# recorded as failed, and /undo and /diff of it stop there, say why and
# change nothing (eukhe_core::undo::tests::
# undo_stops_at_a_turn_without_a_snapshot,
# a_first_turn_without_a_snapshot_is_where_diff_all_starts); /undo is
# refused while a run is going (eukhe_daemon::rpc::commands::tests::
# undo_turn_is_refused_during_the_run_and_get_turn_diff_answers; the SDK:
# embed::undo_turn_is_refused_while_a_run_is_going).

import Base
import ../bend/undo.bend as U
import ../bend/ffi_undo.bend as FU
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# Spec helpers: snapshots
# -----------------------

def sp_act(r: U.St & U.Act) -> U.Act:
  (st, a) = r
  a

def sp_state(r: U.St & U.Act) -> U.St:
  (st, a) = r
  st

# the state after a history, newest first: each event fed to the model in
# the order it happened
def sp_replay(h: List<&2, U.Ev>) -> U.St:
  match h:
    case Nil{}:
      U.St{Nil{}, None{}}
    case Con{e, older}:
      sp_state(U.step(sp_replay(older), e))

# R1: the turns of the history (newest first) that no later /undo took
# back, with k undos later than the head still to take back a turn
def sp_live(h: List<&2, U.Ev>, k: Nat) -> List<&2, Nat>:
  match h:
    case Nil{}:
      Nil{}
    case Con{e, older}:
      match e:
        case U.TurnStart{t}:
          match k:
            case 0n:
              t <> sp_live(older, 0n)
            case 1n+j:
              sp_live(older, j)
        case U.Undo{}:
          sp_live(older, 1n+k)
        case U.Diff{s}:
          sp_live(older, k)

def sp_first.of(m: Maybe<&2, Nat>, e: U.Ev) -> Maybe<&2, Nat>:
  match m:
    case Some{t}:
      Some{t}
    case None{}:
      match e:
        case U.TurnStart{t}:
          Some{t}
        case U.Undo{}:
          None{}
        case U.Diff{s}:
          None{}

# R1: the oldest turn of the history
def sp_first(h: List<&2, U.Ev>) -> Maybe<&2, Nat>:
  match h:
    case Nil{}:
      None{}
    case Con{e, older}:
      sp_first.of(sp_first(older), e)

# R2: the answer of /undo over the turns not undone
def sp_undo(live: List<&2, Nat>) -> U.Act:
  match live:
    case Nil{}:
      U.Refused{}
    case Con{t, rest}:
      U.Restore{t}

# R4: the answer of /diff against a snapshot, if any
def sp_cmp(m: Maybe<&2, Nat>) -> U.Act:
  match m:
    case None{}:
      U.NoSnapshot{}
    case Some{t}:
      U.Compare{t}

def sp_head(xs: List<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, t}:
      Some{x}

# Spec helpers: rows
# ------------------

def sp_nat_eq(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+y:
      False{}
    case 1n+x 0n:
      False{}
    case 1n+x 1n+y:
      sp_nat_eq(x, y)

# two contents are the same: both absent, or the same blob
def sp_same(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case None{} Some{y}:
      False{}
    case Some{x} None{}:
      False{}
    case Some{x} Some{y}:
      sp_nat_eq(x, y)

# R5: a row's content after a fix: None when the fix cannot be carried out
# (writing a snapshot content the snapshot does not have)
def sp_apply(r: U.Row, f: U.Fix) -> Maybe<&2, Maybe<&2, Nat>>:
  match r:
    case U.Row{b, n, h}:
      match b:
        case None{}:
          match f:
            case U.Keep{}:
              Some{n}
            case U.Remove{}:
              Some{None{}}
            case U.Write{}:
              None{}
        case Some{x}:
          match f:
            case U.Keep{}:
              Some{n}
            case U.Remove{}:
              Some{None{}}
            case U.Write{}:
              Some{Some{x}}

def sp_after.cons(m: Maybe<&2, Maybe<&2, Nat>>, rest: Maybe<&2, List<&2, Maybe<&2, Nat>>>) -> Maybe<&2, List<&2, Maybe<&2, Nat>>>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      match rest:
        case None{}:
          None{}
        case Some{cs}:
          Some{c <> cs}

# R5: the rows' contents after one fix per row, in order; None when a fix
# cannot be carried out or the fixes are not one per row
def sp_after(rows: List<&2, U.Row>, fs: List<&2, U.Fix>) -> Maybe<&2, List<&2, Maybe<&2, Nat>>>:
  match rows fs:
    case Nil{} Nil{}:
      Some{Nil{}}
    case Nil{} Con{f, t}:
      None{}
    case Con{r, rs} Nil{}:
      None{}
    case Con{+r, rs} Con{f, t}:
      sp_after.cons(sp_apply(r, f), sp_after(rs, t))

# R5: the content each row must have after /undo
def sp_goal(rows: List<&2, U.Row>) -> List<&2, Maybe<&2, Nat>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case U.Row{b, n, h}:
          match h:
            case True{}:
              n <> sp_goal(t)
            case False{}:
              b <> sp_goal(t)

# R6: each fix leaves its row alone
def sp_kept(fs: List<&2, U.Fix>) -> List<&2, Bool>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case U.Keep{}:
          True{} <> sp_kept(t)
        case U.Remove{}:
          False{} <> sp_kept(t)
        case U.Write{}:
          False{} <> sp_kept(t)

# R6: each row is to be left alone: held, or the same content
def sp_alone(rows: List<&2, U.Row>) -> List<&2, Bool>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case U.Row{b, n, h}:
          Bool.or(h, sp_same(b, n)) <> sp_alone(t)

# R7: what /diff says of a row that is not held
def sp_seen_of(same: Bool) -> U.Seen:
  match same:
    case True{}:
      U.Same{}
    case False{}:
      U.Differs{}

# R7: what /diff says of each row
def sp_seens(rows: List<&2, U.Row>) -> List<&2, U.Seen>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case U.Row{b, n, h}:
          match h:
            case True{}:
              U.Skipped{} <> sp_seens(t)
            case False{}:
              sp_seen_of(sp_same(b, n)) <> sp_seens(t)

# Spec helpers: the wire (R8)
# ---------------------------

def sp_w_maybe(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{t}:
      1n+t

def sp_w_ev(e: U.Ev) -> Nat:
  match e:
    case U.Undo{}:
      0n
    case U.Diff{s}:
      match s:
        case U.Turn{}:
          1n
        case U.All{}:
          2n
    case U.TurnStart{t}:
      3n+t

def sp_w_held(h: Bool) -> Nat:
  match h:
    case False{}:
      0n
    case True{}:
      1n

# the rows as Nats, three per row
def sp_flat(rows: List<&2, U.Row>) -> List<&2, Nat>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case U.Row{b, n, h}:
          sp_w_maybe(b) <> (sp_w_maybe(n) <> (sp_w_held(h) <> sp_flat(t)))

def sp_w_req(q: FU.Req, rest: String) -> String:
  match q:
    case FU.QStep{st, e}:
      match st:
        case U.St{+live, b}:
          Wr.put_nat(0n, LawsBase.wire_spell_nats(live, Wr.put_nat(sp_w_maybe(b), Wr.put_nat(sp_w_ev(e), rest))))
    case FU.QFix{rows}:
      Wr.put_nat(1n, LawsBase.wire_spell_nats(sp_flat(rows), rest))
    case FU.QSeen{rows}:
      Wr.put_nat(2n, LawsBase.wire_spell_nats(sp_flat(rows), rest))

def sp_w_act(a: U.Act, rest: String) -> String:
  match a:
    case U.Took{}:
      Wr.put_nat(0n, rest)
    case U.Restore{t}:
      Wr.put_nat(1n, Wr.put_nat(t, rest))
    case U.Refused{}:
      Wr.put_nat(2n, rest)
    case U.Compare{t}:
      Wr.put_nat(3n, Wr.put_nat(t, rest))
    case U.NoSnapshot{}:
      Wr.put_nat(4n, rest)

def sp_w_fixes(fs: List<&2, U.Fix>) -> List<&2, Nat>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case U.Keep{}:
          0n <> sp_w_fixes(t)
        case U.Remove{}:
          1n <> sp_w_fixes(t)
        case U.Write{}:
          2n <> sp_w_fixes(t)

def sp_w_seens(ss: List<&2, U.Seen>) -> List<&2, Nat>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      match x:
        case U.Same{}:
          0n <> sp_w_seens(t)
        case U.Differs{}:
          1n <> sp_w_seens(t)
        case U.Skipped{}:
          2n <> sp_w_seens(t)

def sp_w_step(r: U.St & U.Act) -> String:
  (st, a) = r
  match st:
    case U.St{live, b}:
      sp_w_act(a, LawsBase.wire_spell_nats(live, Wr.put_nat(sp_w_maybe(b), "")))

# the reply R8 gives a request: the model's answer (pinned by the R1-R7
# laws), spelled
def sp_w_reply(q: FU.Req) -> String:
  match q:
    case FU.QStep{st, e}:
      sp_w_step(U.step(st, e))
    case FU.QFix{rows}:
      LawsBase.wire_spell_nats(sp_w_fixes(U.fixes(rows)), "")
    case FU.QSeen{rows}:
      LawsBase.wire_spell_nats(sp_w_seens(U.seens(rows)), "")

def sp_fit_nats(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# every number and count of the request fits the wire
def sp_fit_req(q: FU.Req) -> Bool:
  match q:
    case FU.QStep{st, e}:
      match st:
        case U.St{live, b}:
          Bool.and(sp_fit_nats(live), Bool.and(LawsBase.wire_fits(sp_w_maybe(b)), LawsBase.wire_fits(sp_w_ev(e))))
    case FU.QFix{rows}:
      sp_fit_nats(sp_flat(rows))
    case FU.QSeen{rows}:
      sp_fit_nats(sp_flat(rows))

# Laws: snapshots
# ---------------

# LAW undo_state (R1): after every history (newest first), the snapshots
# not undone are the turns no later /undo took back, newest first, and the
# session's first snapshot is the oldest turn of the history
# EXCLUDES: /undo that drops the oldest snapshot, or two, or none; a
#   refused /undo that later takes back a newer turn; a turn after undos
#   that brings an undone snapshot back; a first snapshot that moves to a
#   later turn or is lost on /undo
law undo_state:
  for +h: List<&2, U.Ev>
  {sp_replay(h) == U.St{sp_live(h, 0n), sp_first(h)} : U.St}

# LAW undo_restores_newest (R2): after every history, /undo restores the
# newest turn no /undo took back, and is refused when there is none
# EXCLUDES: /undo that restores the oldest snapshot, an undone one, or
#   restores something when none is left
law undo_restores_newest:
  for +h: List<&2, U.Ev>
  {sp_act(U.step(sp_replay(h), U.Undo{})) == sp_undo(sp_live(h, 0n)) : U.Act}

# LAW undo_turn_takes (R2): from every state, a turn start answers that its
# snapshot is kept, so only /undo restores
# EXCLUDES: a turn start that restores the newest snapshot (the previous
#   prompt's work reverted with no /undo), compares, or is refused
law undo_turn_takes:
  for +st: U.St
  for t: Nat
  {sp_act(U.step(st, U.TurnStart{t})) == U.Took{} : U.Act}

# LAW undo_turn_any_state (R2): from every state, whatever its first
# snapshot (none recorded included), a turn start t puts t newest in front
# of the snapshots left and keeps them all; it keeps the first snapshot
# when one is recorded and makes t the first when none is
# EXCLUDES: a turn start that drops or replaces a snapshot left (on a
#   state no history builds, as the wire may carry), moves a recorded
#   first snapshot, or leaves none recorded
law undo_turn_any_state:
  for t: Nat
  for live: List<&2, Nat>
  for f: Nat
  {sp_state(U.step(U.St{live, None{}}, U.TurnStart{t})) == U.St{t <> live, Some{t}} : U.St} & {sp_state(U.step(U.St{live, Some{f}}, U.TurnStart{t})) == U.St{t <> live, Some{f}} : U.St}

# LAW undo_takes_newest (R2): from every state with a snapshot left, for
# every first snapshot (none recorded included), /undo restores the newest
# one and leaves the rest and the first snapshot
# EXCLUDES: /undo refused while a turn is left (on a state no history
#   builds, as the wire may carry), restoring an older turn, dropping two
#   turns or none, or the first snapshot changed
law undo_takes_newest:
  for t: Nat
  for rest: List<&2, Nat>
  for b: Maybe<&2, Nat>
  {U.step(U.St{t <> rest, b}, U.Undo{}) == (U.St{rest, b}, U.Restore{t}) : U.St & U.Act}

# LAW undo_refused_changes_nothing (R3): /undo with no snapshot left, for
# every first snapshot, is refused and leaves the snapshots as they are
# EXCLUDES: a refused /undo that drops the first snapshot
law undo_refused_changes_nothing:
  for +b: Maybe<&2, Nat>
  {U.step(U.St{Nil{}, b}, U.Undo{}) == (U.St{Nil{}, b}, U.Refused{}) : U.St & U.Act}

# LAW undo_refusal_keeps_state (R3): from every state, a /undo the model
# refuses leaves the snapshots as they are (whatever made it refuse)
# EXCLUDES: a refusal, on any state, that drops the first snapshot, or
#   drops, adds or reorders a turn
law undo_refusal_keeps_state:
  for +st: U.St
  for r: {sp_act(U.step(st, U.Undo{})) == U.Refused{} : U.Act}
  {sp_state(U.step(st, U.Undo{})) == st : U.St}

# LAW undo_diff_compares (R4): after every history, /diff of the turn
# compares with the newest turn no /undo took back, /diff all with the
# oldest turn of the history; nothing to compare when there is none
# EXCLUDES: the turn compared with the session's first snapshot, all
#   compared with an undone turn's successor, a comparison with no snapshot
law undo_diff_compares:
  for +h: List<&2, U.Ev>
  {sp_act(U.step(sp_replay(h), U.Diff{U.Turn{}})) == sp_cmp(sp_head(sp_live(h, 0n))) : U.Act} & {sp_act(U.step(sp_replay(h), U.Diff{U.All{}})) == sp_cmp(sp_first(h)) : U.Act}

# LAW undo_diff_any_state (R4): from every state, whatever its first
# snapshot (none recorded included): /diff of the turn compares with the
# newest turn when one is left and finds no snapshot when none is; /diff
# all compares with the first snapshot when one is recorded and finds no
# snapshot when none is
# EXCLUDES: the turn's comparison decided by the first snapshot (no
#   comparison while a turn is left, on a state no history builds, as the
#   wire may carry), the turn compared with an older turn or the first
#   snapshot, all compared with the newest turn, a comparison with no
#   snapshot
law undo_diff_any_state:
  for t: Nat
  for rest: List<&2, Nat>
  for live: List<&2, Nat>
  for b: Maybe<&2, Nat>
  for f: Nat
  {sp_act(U.step(U.St{t <> rest, b}, U.Diff{U.Turn{}})) == U.Compare{t} : U.Act} & {sp_act(U.step(U.St{Nil{}, b}, U.Diff{U.Turn{}})) == U.NoSnapshot{} : U.Act} & {sp_act(U.step(U.St{live, Some{f}}, U.Diff{U.All{}})) == U.Compare{f} : U.Act} & {sp_act(U.step(U.St{live, None{}}, U.Diff{U.All{}})) == U.NoSnapshot{} : U.Act}

# LAW undo_diff_keeps (R4): /diff, of either scope, from every state,
# leaves the snapshots as they are
# EXCLUDES: a /diff that drops or adds a snapshot
law undo_diff_keeps:
  for +st: U.St
  for +s: U.Scope
  {sp_state(U.step(st, U.Diff{s})) == st : U.St}

# LAW undo_example (R1, R2): anchor: turns 1 and 2, /undo (2 restored),
# turn 3: the snapshots are 3 then 1, the first is 1, and two /undo restore
# 3 then 1
# EXCLUDES: a model wrong on the documented case
law undo_example:
  {sp_replay([U.TurnStart{3n}, U.Undo{}, U.TurnStart{2n}, U.TurnStart{1n}]) == U.St{[3n, 1n], Some{1n}} : U.St} &
  {sp_act(U.step(sp_replay([U.Undo{}, U.TurnStart{3n}, U.Undo{}, U.TurnStart{2n}, U.TurnStart{1n}]), U.Undo{})) == U.Restore{1n} : U.Act}

# Laws: rows
# ----------

# LAW undo_restores_rows (R5): for every list of rows, the fixes /undo
# answers are one per row and leave each row that is not held with the
# snapshot's content (a path absent from the snapshot removed) and each
# held row with the workspace's content
# EXCLUDES: a path added since left in place, a removed path not written
#   back, a changed path kept, a held path removed or overwritten, a write
#   for a path the snapshot does not have, a fix dropped or added
law undo_restores_rows:
  for +rows: List<&2, U.Row>
  {sp_after(rows, U.fixes(rows)) == Some{sp_goal(rows)} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}

# LAW undo_touches_only_changed (R6): for every list of rows, /undo leaves
# alone exactly the rows that are held or have the same content
# EXCLUDES: a held path written with its own content, an unchanged path
#   rewritten, a changed path left alone
law undo_touches_only_changed:
  for +rows: List<&2, U.Row>
  {sp_kept(U.fixes(rows)) == sp_alone(rows) : List<&2, Bool>}

# LAW undo_diff_rows (R7): for every list of rows, /diff skips the held
# rows, calls the rows with the same content the same, and every other row
# different, one answer per row in order
# EXCLUDES: a held path listed as different, an unchanged path listed, a
#   changed path left out, an answer dropped
law undo_diff_rows:
  for +rows: List<&2, U.Row>
  {U.seens(rows) == sp_seens(rows) : List<&2, U.Seen>}

# Laws: the entry (R8)
# --------------------

# LAW undo_entry_answers (R8): the entry answers every request Rust
# spells, every number within the wire, with the spelled answer of the
# model (pinned by the R1-R7 laws)
# EXCLUDES: the questions swapped, fields read in another order, a held
#   flag misread, a default
law undo_entry_answers:
  for +q: FU.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FU.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW undo_entry_exact (R8): every input the entry does not answer with the
# error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown tag, a row
#   cut short, a held flag past 1, input left over)
law undo_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FU.ffi(s)) == False{} : Bool}
  exs r: FU.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW undo_entry_req_exact (R8): the entry's decoder reads a request only
# from a spelled one: whatever it decodes is a request whose every number
# fits the wire, spelled, then the input after it
# EXCLUDES: a decoder that invents a request (a default request for an
#   unknown tag, empty or short input), reads a number with a leading zero
#   or past the wire
law undo_entry_req_exact:
  for +s: String
  for +q: FU.Req
  for +rest: String
  for +h: {FU.get_req(s) == Wr.Got{q, rest} : Wr.Dec<FU.Req>}
  {s == sp_w_req(q, rest) : String} & {sp_fit_req(q) == True{} : Bool}

# LAW undo_entry_req_example (R8): anchor: an unknown tag, a tag with a
# leading zero and empty input are no request
# EXCLUDES: a default request for an unknown tag or empty input
law undo_entry_req_example:
  {[FU.get_req("3,"), FU.get_req("01,"), FU.get_req("")] == [Wr.Bad{}, Wr.Bad{}, Wr.Bad{}] : List<&2, Wr.Dec<FU.Req>>}

# LAW undo_entry_refuses (R8): every error the entry answers is exactly
# `E undo: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law undo_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FU.ffi(s)) == True{} : Bool}
  {FU.ffi(s) == Wr.err("undo: malformed request") : String}

# LAW undo_entry_example (R8): anchor: the wire strings Rust sends and the
# replies it reads; a row cut short, a held flag of 2, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law undo_entry_example:
  {[FU.ffi("0,2,3,1,2,0,"), FU.ffi("0,0,0,5,"), FU.ffi("1,6,1,0,0,0,4,1,"), FU.ffi("2,6,1,2,0,3,3,1,"), FU.ffi("1,2,1,0,"), FU.ffi("1,3,1,0,2,"), FU.ffi("0,0,0,0,x")] == ["1,3,1,1,2,", "0,1,2,3,", "2,2,0,", "2,1,2,", Wr.err("undo: malformed request"), Wr.err("undo: malformed request"), Wr.err("undo: malformed request")] : List<&2, String>}

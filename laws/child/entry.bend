# eukhe: the laws of area child: the child entry (bend/ffi_child.bend) on
# the requests Rust writes, and its wire spelled from the wire primitives

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# ---- core_w6 ----

# LAWS: the entries of the compiled Bend core for the child task, the jobs,
# the goal's progress check and the hand-back (bend/ffi_child.bend,
# bend/ffi_job.bend, bend/ffi_progress.bend, bend/ffi_sandbox.bend). Each
# entry, on the request Rust writes (`put_req`, every number within the
# wire), answers the encoding of the model's decision: the codec loses,
# invents and reorders nothing, and the Rust rule is the proven model.

def wire_cfg_fits(c: Ch.Cfg) -> Bool:
  match c:
    case Ch.Cfg{s, f}:
      Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(f))

def wire_w_fits(w: Ch.W) -> Bool:
  match w:
    case Ch.W{t, l, n}:
      Bool.and(LawsBase.wire_mfits(t), Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(n)))

def wire_obs_fits(o: Ch.Obs) -> Bool:
  match o:
    case Ch.Busy{t}:
      LawsBase.wire_mfits(t)
    case Ch.PollFailed{}:
      True{}
    case Ch.Answered{r}:
      True{}
    case Ch.Broke{}:
      True{}
    case Ch.Gone{}:
      True{}

def wire_ph_fits(p: Ch.Ph) -> Bool:
  match p:
    case Ch.Watching{w}:
      wire_w_fits(w)
    case Ch.Owing{k, n}:
      LawsBase.wire_fits(n)
    case Ch.Ended{}:
      True{}

# LAW child_entry_verdict: the child entry's verdict request answers the task's call
# EXCLUDES: a codec that drops or swaps a field, a default for a field
law child_entry_verdict:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +o: Ch.Obs
  for +m: Ch.Mode
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for he: {LawsBase.wire_fits(e) == True{} : Bool}
  for ho: {wire_obs_fits(o) == True{} : Bool}
  {FCh.ffi(FCh.put_req(FCh.AskVerdict{c, w, e, o, m})) == FCh.put_call(Ch.verdict(c, w, e, o, m), "") : String}

# LAW child_entry_move: the child entry's move request answers the report phase's move
law child_entry_move:
  for +f: Maybe<&2, Ch.Fate>
  for +n: Nat
  for hn: {LawsBase.wire_fits(n) == True{} : Bool}
  {FCh.ffi(FCh.put_req(FCh.AskMove{f, n})) == FCh.put_move(Ch.owe.next(f, n), "") : String}

# LAW child_entry_abort: the child entry's abort request answers the abort's phase
law child_entry_abort:
  for +p: Ch.Ph
  for +d: Bool
  for hp: {wire_ph_fits(p) == True{} : Bool}
  {FCh.ffi(FCh.put_req(FCh.AskAbort{p, d})) == FCh.put_ph(Ch.cut.ph(p, d), "") : String}

# The child entry's wire, spelled from the wire primitives only (never the
# entry's own put_*): the grammar of bend/ffi_child.bend's header. A
# constructor is Wr.put_nat(<its tag>, <its fields>); a record is its
# fields in order; a Maybe is tag 0 (None) or tag 1 then the value.

# a Maybe<Nat>: 0 none, 1 then the Nat
def ch_spell_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))

# the watch's clock: the token, left, tries
def ch_spell_w(w: Ch.W, rest: String) -> String:
  match w:
    case Ch.W{t, l, n}:
      ch_spell_mnat(t, Wr.put_nat(l, Wr.put_nat(n, rest)))

# the settings: stall, fails
def ch_spell_cfg(c: Ch.Cfg, rest: String) -> String:
  match c:
    case Ch.Cfg{s, f}:
      Wr.put_nat(s, Wr.put_nat(f, rest))

# a poll: Busy 0 (token), PollFailed 1, Answered 2 (Bool), Broke 3, Gone 4
def ch_spell_obs(o: Ch.Obs, rest: String) -> String:
  match o:
    case Ch.Busy{t}:
      Wr.put_nat(0n, ch_spell_mnat(t, rest))
    case Ch.PollFailed{}:
      Wr.put_nat(1n, rest)
    case Ch.Answered{r}:
      Wr.put_nat(2n, Wr.put_bool(r, rest))
    case Ch.Broke{}:
      Wr.put_nat(3n, rest)
    case Ch.Gone{}:
      Wr.put_nat(4n, rest)

# a mode: Inbox 0, Silent 1
def ch_spell_mode(m: Ch.Mode, rest: String) -> String:
  match m:
    case Ch.Inbox{}:
      Wr.put_nat(0n, rest)
    case Ch.Silent{}:
      Wr.put_nat(1n, rest)

# a report: Completed 0, Failed 1, Cancelled 2, Stalled 3, Unreachable 4
def ch_spell_report(k: Ch.Report, rest: String) -> String:
  match k:
    case Ch.Completed{}:
      Wr.put_nat(0n, rest)
    case Ch.Failed{}:
      Wr.put_nat(1n, rest)
    case Ch.Cancelled{}:
      Wr.put_nat(2n, rest)
    case Ch.Stalled{}:
      Wr.put_nat(3n, rest)
    case Ch.Unreachable{}:
      Wr.put_nat(4n, rest)

# a Maybe<Report>: 0 none, 1 then the report
def ch_spell_mreport(m: Maybe<&2, Ch.Report>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{k}:
      Wr.put_nat(1n, ch_spell_report(k, rest))

# a call: Watches 0 (clock), Reports 1 (report), Settles 2 (Maybe<Report>)
def ch_spell_call(c: Ch.Call, rest: String) -> String:
  match c:
    case Ch.Watches{w}:
      Wr.put_nat(0n, ch_spell_w(w, rest))
    case Ch.Reports{k}:
      Wr.put_nat(1n, ch_spell_report(k, rest))
    case Ch.Settles{why}:
      Wr.put_nat(2n, ch_spell_mreport(why, rest))

# a fate: Queued 0, Withdrawn 1, Placed 2, Read 3
def ch_spell_fate(f: Ch.Fate, rest: String) -> String:
  match f:
    case Ch.Queued{}:
      Wr.put_nat(0n, rest)
    case Ch.Withdrawn{}:
      Wr.put_nat(1n, rest)
    case Ch.Placed{}:
      Wr.put_nat(2n, rest)
    case Ch.Read{}:
      Wr.put_nat(3n, rest)

# a Maybe<Fate>: 0 none, 1 then the fate
def ch_spell_mfate(f: Maybe<&2, Ch.Fate>, rest: String) -> String:
  match f:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, ch_spell_fate(x, rest))

# a move: Submit 0 (id), Await 1, Resubmit 2 (id), Delivered 3
def ch_spell_move(m: Ch.Move, rest: String) -> String:
  match m:
    case Ch.Submit{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case Ch.Await{}:
      Wr.put_nat(1n, rest)
    case Ch.Resubmit{n}:
      Wr.put_nat(2n, Wr.put_nat(n, rest))
    case Ch.Delivered{}:
      Wr.put_nat(3n, rest)

# a phase: Watching 0 (clock), Owing 1 (report, id), Ended 2
def ch_spell_ph(p: Ch.Ph, rest: String) -> String:
  match p:
    case Ch.Watching{w}:
      Wr.put_nat(0n, ch_spell_w(w, rest))
    case Ch.Owing{k, n}:
      Wr.put_nat(1n, ch_spell_report(k, Wr.put_nat(n, rest)))
    case Ch.Ended{}:
      Wr.put_nat(2n, rest)

# a request: 0 verdict (settings, clock, elapsed ms, poll, mode), 1 move
# (fate, id), 2 abort (phase, delete flag), then rest
def ch_spell_req(r: FCh.Req, rest: String) -> String:
  match r:
    case FCh.AskVerdict{c, w, e, o, m}:
      Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, Wr.put_nat(e, ch_spell_obs(o, ch_spell_mode(m, rest))))))
    case FCh.AskMove{f, n}:
      Wr.put_nat(1n, ch_spell_mfate(f, Wr.put_nat(n, rest)))
    case FCh.AskAbort{p, d}:
      Wr.put_nat(2n, ch_spell_ph(p, Wr.put_bool(d, rest)))

# every number of a request fits the wire
def ch_req_fits(r: FCh.Req) -> Bool:
  match r:
    case FCh.AskVerdict{c, w, e, o, m}:
      Bool.and(wire_cfg_fits(c), Bool.and(wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), wire_obs_fits(o))))
    case FCh.AskMove{f, n}:
      LawsBase.wire_fits(n)
    case FCh.AskAbort{p, d}:
      wire_ph_fits(p)

# the spelled reply of the model's decision on request r
def ch_spell_answer(r: FCh.Req) -> String:
  match r:
    case FCh.AskVerdict{+c, +w, +e, o, m}:
      ch_spell_call(Ch.verdict(c, w, e, o, m), "")
    case FCh.AskMove{f, +n}:
      ch_spell_move(Ch.owe.next(f, n), "")
    case FCh.AskAbort{p, d}:
      ch_spell_ph(Ch.cut.ph(p, d), "")

# LAW child_entry_answers_spelled: a request spelled by the grammar, every
# number within the wire, is answered with the grammar's spelling of the
# model's decision (the call, the move, the phase)
# EXCLUDES: a request or reply tag that drifts from the grammar Rust reads
#   and writes (a swapped or renumbered tag on either side), a field lost,
#   swapped or defaulted, a reply spelled another way
law child_entry_answers_spelled:
  for +r: FCh.Req
  for fits: {ch_req_fits(r) == True{} : Bool}
  {FCh.ffi(ch_spell_req(r, "")) == ch_spell_answer(r) : String}

# LAW child_entry_left_over: a spelled request that fits, followed by any
# more input, answers the error form "child: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request
law child_entry_left_over:
  for +r: FCh.Req
  for fits: {ch_req_fits(r) == True{} : Bool}
  for +c: Char
  for +t: String
  {FCh.ffi(ch_spell_req(r, SCon{c, t})) == Wr.err("child: input left over") : String}

# LAW child_entry_unknown_request: a request tag of 3 or more (within the
# wire) answers the error form "child: unknown request", whatever follows
# EXCLUDES: an unknown request read as a known one, or as another error
law child_entry_unknown_request:
  for +n: Nat
  for +rest: String
  for fit: {LawsBase.wire_fits(3n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(3n+n, rest)) == Wr.err("child: unknown request") : String}

# LAW child_entry_reads_only_requests: an answer that is not the error
# form answers a request: the input is exactly the spelling of a request
# whose numbers fit the wire, and the answer is the spelled reply of the
# model's decision on it
# EXCLUDES: a decoder that accepts an unknown tag (a poll, mode, fate,
#   report, phase or request tag), a missing or extra field, or input left
#   over, and answers it anyway (a default instead of the error form)
law child_entry_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCh.ffi(s)) == False{} : Bool}
  exs r: FCh.Req
  {(s, (ch_req_fits(r), FCh.ffi(s))) == (ch_spell_req(r, ""), (True{}, ch_spell_answer(r))) : String & (Bool & String)}

# LAW child_entry_tags_example: anchor: the bytes Rust sends and reads for
# a verdict (a lost poll on a clock with one try left: report
# unreachable), a move (no fate yet: submit under 1) and an abort (an
# owed cancelled report goes on); an unknown poll tag (5) and an unknown
# request tag (3) are refused with their exact error bytes
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, an unknown tag read as a known one
law child_entry_tags_example:
  {[FCh.ffi("0,5,2,0,5,1,1,1,0,"), FCh.ffi("1,0,1,"), FCh.ffi("2,1,2,1,F"), FCh.ffi("0,5,2,0,5,1,1,5,0,"), FCh.ffi("3,")] == ["1,4,", "0,1,", "1,2,1,", "E child: bad poll", "E child: unknown request"] : List<&2, String>}

# a is one of the child entry's error replies: the error form of one of the
# texts bend/ffi_child.bend writes
def ch_named_error(+a: String) -> Bool:
  Bool.or(String.eq(a, Wr.err("child: bad request")), Bool.or(String.eq(a, Wr.err("child: unknown request")), Bool.or(String.eq(a, Wr.err("child: bad settings")), Bool.or(String.eq(a, Wr.err("child: bad clock")), Bool.or(String.eq(a, Wr.err("child: bad elapsed ms")), Bool.or(String.eq(a, Wr.err("child: bad poll")), Bool.or(String.eq(a, Wr.err("child: bad mode")), Bool.or(String.eq(a, Wr.err("child: input left over")), Bool.or(String.eq(a, Wr.err("child: bad fate")), Bool.or(String.eq(a, Wr.err("child: bad id")), Bool.or(String.eq(a, Wr.err("child: bad phase")), String.eq(a, Wr.err("child: bad delete flag")))))))))))))

# LAW child_entry_errors_named: every error reply of the entry (an answer
# that opens with 'E') is one of the entry's named texts in the error
# form: "child: " then bad request, unknown request, bad settings, bad
# clock, bad elapsed ms, bad poll, bad mode, input left over, bad fate,
# bad id, bad phase or bad delete flag (ch_named_error, the texts
# bend/ffi_child.bend writes); which input gets which text is pinned by
# the laws below
# EXCLUDES: an error reply with a text not among these twelve (an
#   unprefixed, reworded or empty text)
law child_entry_errors_named:
  for +s: String
  for err: {LawsBase.wire_opens_err(FCh.ffi(s)) == True{} : Bool}
  {ch_named_error(FCh.ffi(s)) == True{} : Bool}

# LAW child_entry_unknown_token: in a verdict request, a clock token tag
# past 1 (none, some) answers "child: bad clock", whatever follows
# EXCLUDES: an unknown token tag read as none or some, or named as another
#   field
law child_entry_unknown_token:
  for +c: Ch.Cfg
  for +n: Nat
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for fit: {LawsBase.wire_fits(2n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, Wr.put_nat(2n+n, rest)))) == Wr.err("child: bad clock") : String}

# LAW child_entry_unknown_poll: in a verdict request, a poll tag past 4
# answers "child: bad poll", whatever follows
# EXCLUDES: an unknown poll read as a known one (the old TBad-as-PollFailed
#   mutant), or named as another field
law child_entry_unknown_poll:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +n: Nat
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for he: {LawsBase.wire_fits(e) == True{} : Bool}
  for fit: {LawsBase.wire_fits(5n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, Wr.put_nat(e, Wr.put_nat(5n+n, rest)))))) == Wr.err("child: bad poll") : String}

# LAW child_entry_unknown_mode: in a verdict request, a mode tag past 1
# (inbox, silent) answers "child: bad mode", whatever follows
# EXCLUDES: an unknown mode read as inbox or silent, or named as another
#   field
law child_entry_unknown_mode:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +o: Ch.Obs
  for +n: Nat
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for he: {LawsBase.wire_fits(e) == True{} : Bool}
  for ho: {wire_obs_fits(o) == True{} : Bool}
  for fit: {LawsBase.wire_fits(2n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, Wr.put_nat(e, ch_spell_obs(o, Wr.put_nat(2n+n, rest))))))) == Wr.err("child: bad mode") : String}

# LAW child_entry_unknown_mfate: in a move request, a fate presence tag
# past 1 (none, some) answers "child: bad fate", whatever follows
# EXCLUDES: an unknown presence tag read as none or some
law child_entry_unknown_mfate:
  for +n: Nat
  for +rest: String
  for fit: {LawsBase.wire_fits(2n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(1n, Wr.put_nat(2n+n, rest))) == Wr.err("child: bad fate") : String}

# LAW child_entry_unknown_fate: in a move request, a fate tag past 3
# (queued, withdrawn, placed, read) answers "child: bad fate", whatever
# follows
# EXCLUDES: an unknown fate read as a known one
law child_entry_unknown_fate:
  for +n: Nat
  for +rest: String
  for fit: {LawsBase.wire_fits(4n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(1n, Wr.put_nat(1n, Wr.put_nat(4n+n, rest)))) == Wr.err("child: bad fate") : String}

# LAW child_entry_unknown_phase: in an abort request, a phase tag past 2
# (watching, owing, ended) answers "child: bad phase", whatever follows
# EXCLUDES: an unknown phase read as a known one
law child_entry_unknown_phase:
  for +n: Nat
  for +rest: String
  for fit: {LawsBase.wire_fits(3n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(2n, Wr.put_nat(3n+n, rest))) == Wr.err("child: bad phase") : String}

# LAW child_entry_unknown_report: in an abort request, an owing phase's
# report tag past 4 answers "child: bad phase", whatever follows
# EXCLUDES: an unknown report read as a known one
law child_entry_unknown_report:
  for +n: Nat
  for +rest: String
  for fit: {LawsBase.wire_fits(5n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(2n, Wr.put_nat(1n, Wr.put_nat(5n+n, rest)))) == Wr.err("child: bad phase") : String}

# LAW child_entry_errors_example: anchor: each field cut short names
# itself: no request, then the settings, clock, elapsed ms, poll and mode
# of a verdict, the fate and id of a move, the phase and delete flag of an
# abort
# EXCLUDES: two error texts swapped, a field's error named as another
law child_entry_errors_example:
  {[FCh.ffi(""), FCh.ffi("0,"), FCh.ffi("0,5,2,"), FCh.ffi("0,5,2,0,5,1,"), FCh.ffi("0,5,2,0,5,1,1,"), FCh.ffi("0,5,2,0,5,1,1,1,"), FCh.ffi("1,"), FCh.ffi("1,0,"), FCh.ffi("2,"), FCh.ffi("2,2,")] == [Wr.err("child: bad request"), Wr.err("child: bad settings"), Wr.err("child: bad clock"), Wr.err("child: bad elapsed ms"), Wr.err("child: bad poll"), Wr.err("child: bad mode"), Wr.err("child: bad fate"), Wr.err("child: bad id"), Wr.err("child: bad phase"), Wr.err("child: bad delete flag")] : List<&2, String>}

# Each field refused, by name
# ---------------------------
# A request field that does not read names itself. For each field F: the
# fields before F spelled by the grammar above (every number within the
# wire), then input where F's next primitive does not read (Wr.get_nat or
# Wr.get_bool answers Bad{}: nothing left, not a number, a leading zero,
# too many digits, not T or F), whatever follows, answers the error form
# of F's text. The texts are the ones bend/ffi_child.bend writes, the wire
# contract Rust reads: "child: bad request", "child: bad settings",
# "child: bad clock", "child: bad elapsed ms", "child: bad poll", "child:
# bad mode", "child: bad fate", "child: bad id", "child: bad phase",
# "child: bad delete flag". These laws pin which field is blamed. With
# the unknown-tag laws above (a tag that reads but names no constructor),
# child_entry_answers_spelled and child_entry_left_over (a whole request)
# and the wire's exactness laws (a primitive that reads is its own
# spelling, within the wire), every input falls under one of them.
#
# A cut is where, inside a field of several primitives, the one that does
# not read stands; ch_cut_* spells what of the field comes before it.

# the settings: before the stall, or after the stall s (before the fails)
type ChSetCut is Data:
  SetAtStall{}
  SetAtFails{s: Nat}

def ch_cut_set(k: ChSetCut, rest: String) -> String:
  match k:
    case SetAtStall{}:
      rest
    case SetAtFails{s}:
      Wr.put_nat(s, rest)

def ch_cut_set_fits(k: ChSetCut) -> Bool:
  match k:
    case SetAtStall{}:
      True{}
    case SetAtFails{s}:
      LawsBase.wire_fits(s)

# a clock: before the token's tag, after tag 1 (before the token), after
# the token t (before left), after the token t and left l (before tries)
type ChClockCut is Data:
  ClkAtTag{}
  ClkAtToken{}
  ClkAtLeft{t: Maybe<&2, Nat>}
  ClkAtTries{t: Maybe<&2, Nat>, l: Nat}

def ch_cut_clock(k: ChClockCut, rest: String) -> String:
  match k:
    case ClkAtTag{}:
      rest
    case ClkAtToken{}:
      Wr.put_nat(1n, rest)
    case ClkAtLeft{t}:
      ch_spell_mnat(t, rest)
    case ClkAtTries{t, l}:
      ch_spell_mnat(t, Wr.put_nat(l, rest))

def ch_cut_clock_fits(k: ChClockCut) -> Bool:
  match k:
    case ClkAtTag{}:
      True{}
    case ClkAtToken{}:
      True{}
    case ClkAtLeft{t}:
      LawsBase.wire_mfits(t)
    case ClkAtTries{t, l}:
      Bool.and(LawsBase.wire_mfits(t), LawsBase.wire_fits(l))

# a poll: before its tag, after Busy's tag 0 (before the token's tag),
# after Busy 0 and the token's tag 1 (before the token)
type ChPollCut is Data:
  PollAtTag{}
  PollAtBusyTag{}
  PollAtBusyToken{}

def ch_cut_poll(k: ChPollCut, rest: String) -> String:
  match k:
    case PollAtTag{}:
      rest
    case PollAtBusyTag{}:
      Wr.put_nat(0n, rest)
    case PollAtBusyToken{}:
      Wr.put_nat(0n, Wr.put_nat(1n, rest))

# a fate presence: before its tag, after tag 1 (before the fate's tag)
type ChFateCut is Data:
  FateAtPresence{}
  FateAtTag{}

def ch_cut_fate(k: ChFateCut, rest: String) -> String:
  match k:
    case FateAtPresence{}:
      rest
    case FateAtTag{}:
      Wr.put_nat(1n, rest)

# a phase: before its tag, inside Watching's clock (after tag 0), after
# Owing's tag 1 (before the report), after Owing 1 and report r (before
# the id)
type ChPhaseCut is Data:
  PhAtTag{}
  PhAtClock{c: ChClockCut}
  PhAtReport{}
  PhAtOwedId{r: Ch.Report}

def ch_cut_phase(k: ChPhaseCut, rest: String) -> String:
  match k:
    case PhAtTag{}:
      rest
    case PhAtClock{c}:
      Wr.put_nat(0n, ch_cut_clock(c, rest))
    case PhAtReport{}:
      Wr.put_nat(1n, rest)
    case PhAtOwedId{r}:
      Wr.put_nat(1n, ch_spell_report(r, rest))

def ch_cut_phase_fits(k: ChPhaseCut) -> Bool:
  match k:
    case PhAtTag{}:
      True{}
    case PhAtClock{c}:
      ch_cut_clock_fits(c)
    case PhAtReport{}:
      True{}
    case PhAtOwedId{r}:
      True{}

# LAW child_entry_bad_request: input whose request tag does not read as a
# number answers "child: bad request"
# EXCLUDES: a missing or malformed request tag read as a request (a
#   default tag) or named as an unknown request
law child_entry_bad_request:
  for +rest: String
  for bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}
  {FCh.ffi(rest) == Wr.err("child: bad request") : String}

# LAW child_entry_bad_settings: in a verdict request, a stall, or a fails
# after a stall within the wire, that does not read as a number answers
# "child: bad settings", whatever the rest
# EXCLUDES: a malformed setting read as a default or named as another
#   field (the clock), a field read past it
law child_entry_bad_settings:
  for +k: ChSetCut
  for +rest: String
  for fit: {ch_cut_set_fits(k) == True{} : Bool}
  for bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}
  {FCh.ffi(Wr.put_nat(0n, ch_cut_set(k, rest))) == Wr.err("child: bad settings") : String}

# LAW child_entry_bad_clock: in a verdict request, after spelled settings
# within the wire, a clock number (the token's tag, the token after tag
# 1, left, tries; what comes before it in the clock within the wire) that
# does not read answers "child: bad clock", whatever the rest
# EXCLUDES: a malformed clock part read as a default or named as another
#   field (the settings or the elapsed ms), a field read past it
law child_entry_bad_clock:
  for +c: Ch.Cfg
  for +k: ChClockCut
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for fit: {ch_cut_clock_fits(k) == True{} : Bool}
  for bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, ch_cut_clock(k, rest)))) == Wr.err("child: bad clock") : String}

# LAW child_entry_bad_elapsed: in a verdict request, after spelled
# settings and clock within the wire, elapsed ms that do not read as a
# number answer "child: bad elapsed ms", whatever the rest
# EXCLUDES: malformed elapsed ms read as a default (0) or named as another
#   field, a field read past them
law child_entry_bad_elapsed:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, rest)))) == Wr.err("child: bad elapsed ms") : String}

# LAW child_entry_bad_poll: in a verdict request, after spelled settings,
# clock and elapsed ms within the wire, a poll number (its tag, a busy
# poll's token tag, the token after tag 1) that does not read answers
# "child: bad poll", whatever the rest
# EXCLUDES: a malformed poll read as a known one (a busy poll with no
#   token, a lost poll) or named as another field (the mode)
law child_entry_bad_poll:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +k: ChPollCut
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for he: {LawsBase.wire_fits(e) == True{} : Bool}
  for bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, Wr.put_nat(e, ch_cut_poll(k, rest)))))) == Wr.err("child: bad poll") : String}

# LAW child_entry_bad_answered: in a verdict request, after spelled
# settings, clock and elapsed ms within the wire, an answered poll (tag 2)
# whose flag does not read as T or F answers "child: bad poll", whatever
# the rest
# EXCLUDES: a malformed answered flag read as a default (no reply) or
#   named as another field (the mode)
law child_entry_bad_answered:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for he: {LawsBase.wire_fits(e) == True{} : Bool}
  for bad: {Wr.get_bool(rest) == Wr.Bad{} : Wr.Dec<Bool>}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, Wr.put_nat(e, Wr.put_nat(2n, rest)))))) == Wr.err("child: bad poll") : String}

# LAW child_entry_unknown_busy_token: in a verdict request, after spelled
# settings, clock and elapsed ms within the wire, a busy poll whose token
# tag is past 1 (none, some) answers "child: bad poll", whatever follows
# EXCLUDES: an unknown busy token tag read as none or some, or named as
#   another field
law child_entry_unknown_busy_token:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +n: Nat
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for he: {LawsBase.wire_fits(e) == True{} : Bool}
  for fit: {LawsBase.wire_fits(2n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, Wr.put_nat(e, Wr.put_nat(0n, Wr.put_nat(2n+n, rest))))))) == Wr.err("child: bad poll") : String}

# LAW child_entry_bad_mode: in a verdict request, after spelled settings,
# clock, elapsed ms and poll within the wire, a mode tag that does not
# read as a number answers "child: bad mode", whatever the rest
# EXCLUDES: a malformed mode read as a default (inbox) or named as input
#   left over
law child_entry_bad_mode:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +o: Ch.Obs
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for he: {LawsBase.wire_fits(e) == True{} : Bool}
  for ho: {wire_obs_fits(o) == True{} : Bool}
  for bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, Wr.put_nat(e, ch_spell_obs(o, rest)))))) == Wr.err("child: bad mode") : String}

# LAW child_entry_bad_fate: in a move request, a fate presence tag, or a
# fate tag after presence 1, that does not read as a number answers
# "child: bad fate", whatever the rest
# EXCLUDES: a malformed fate read as no fate (a first submission) or
#   named as another field (the id)
law child_entry_bad_fate:
  for +k: ChFateCut
  for +rest: String
  for bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}
  {FCh.ffi(Wr.put_nat(1n, ch_cut_fate(k, rest))) == Wr.err("child: bad fate") : String}

# LAW child_entry_bad_id: in a move request, after a spelled fate presence
# (any Maybe<Fate>), an id that does not read as a number answers "child:
# bad id", whatever the rest
# EXCLUDES: a malformed id named as another field or as an unknown request
#   (the "1,0,7" answering "child: unknown request" program)
law child_entry_bad_id:
  for +f: Maybe<&2, Ch.Fate>
  for +rest: String
  for bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}
  {FCh.ffi(Wr.put_nat(1n, ch_spell_mfate(f, rest))) == Wr.err("child: bad id") : String}

# LAW child_entry_bad_phase: in an abort request, a phase number (its
# tag; a watched clock's token tag, token after tag 1, left or tries,
# what comes before it in the clock within the wire; an owed report's
# tag; the owed id after a report) that does not read answers "child:
# bad phase", whatever the rest
# EXCLUDES: a malformed phase read as a known one (an ended task, a
#   default clock or report) or named as another field (the delete flag)
law child_entry_bad_phase:
  for +k: ChPhaseCut
  for +rest: String
  for fit: {ch_cut_phase_fits(k) == True{} : Bool}
  for bad: {Wr.get_nat(rest) == Wr.Bad{} : Wr.Dec<Nat>}
  {FCh.ffi(Wr.put_nat(2n, ch_cut_phase(k, rest))) == Wr.err("child: bad phase") : String}

# LAW child_entry_unknown_watched_token: in an abort request, a watching
# phase whose clock token tag is past 1 (none, some) answers "child: bad
# phase", whatever follows
# EXCLUDES: an unknown watched token tag read as none or some, or named as
#   another field (the delete flag)
law child_entry_unknown_watched_token:
  for +n: Nat
  for +rest: String
  for fit: {LawsBase.wire_fits(2n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(2n, Wr.put_nat(0n, Wr.put_nat(2n+n, rest)))) == Wr.err("child: bad phase") : String}

# LAW child_entry_bad_delete_flag: in an abort request, after a spelled
# phase within the wire, a delete flag that does not read as T or F
# answers "child: bad delete flag", whatever the rest
# EXCLUDES: a malformed delete flag read as a default (a cancel) or named
#   as another field (the phase, input left over)
law child_entry_bad_delete_flag:
  for +p: Ch.Ph
  for +rest: String
  for hp: {wire_ph_fits(p) == True{} : Bool}
  for bad: {Wr.get_bool(rest) == Wr.Bad{} : Wr.Dec<Bool>}
  {FCh.ffi(Wr.put_nat(2n, ch_spell_ph(p, rest))) == Wr.err("child: bad delete flag") : String}

# LAW child_quiet_poll_example: anchor, on the bytes Rust sends: settings
# stall 5, fails 2; clock token 7, 1 ms left, 2 tries; 1 ms elapsed; a
# busy poll with token 7 (no news) in inbox mode reports stalled; with 3
# ms left it watches on with 2 ms left and the tries full; a failed poll
# on 3 ms and 3 tries left watches on with 2 ms and 2 tries left
# EXCLUDES: a busy poll with no news that never spends the elapsed ms (a
#   child hung while busy watched forever), a failed poll that spends no
#   time or no try
law child_quiet_poll_example:
  {[FCh.ffi("0,5,2,1,7,1,2,1,0,1,7,0,"), FCh.ffi("0,5,2,1,7,3,2,1,0,1,7,0,"), FCh.ffi("0,5,2,1,7,3,3,1,1,0,")] == ["1,3,", "0,1,7,2,2,", "0,1,7,2,2,"] : List<&2, String>}

# LAW child_entry_malformed_example: anchor: a field that is there but
# does not read (not a number, an unknown tag, not T or F) names itself:
# the request tag; the settings; the clock's token tag, token, left and
# tries; the elapsed ms; the poll's tag, busy token and answered flag; the
# mode; the fate's presence and tag; the id; the phase's tag, watched
# clock, owed report and owed id; the delete flag
# EXCLUDES: a malformed field named as another field, a field read past a
#   malformed one
law child_entry_malformed_example:
  {[FCh.ffi("x"), FCh.ffi("0,x"), FCh.ffi("0,5,x"), FCh.ffi("0,5,2,7,"), FCh.ffi("0,5,2,1,x"), FCh.ffi("0,5,2,0,x"), FCh.ffi("0,5,2,0,5,x"), FCh.ffi("0,5,2,0,5,1,x"), FCh.ffi("0,5,2,0,5,1,1,x"), FCh.ffi("0,5,2,0,5,1,1,0,x"), FCh.ffi("0,5,2,0,5,1,1,2,x"), FCh.ffi("0,5,2,0,5,1,1,1,x"), FCh.ffi("1,x"), FCh.ffi("1,1,x"), FCh.ffi("1,0,7"), FCh.ffi("2,x"), FCh.ffi("2,0,x"), FCh.ffi("2,1,x"), FCh.ffi("2,1,0,x"), FCh.ffi("2,2,x")] == [Wr.err("child: bad request"), Wr.err("child: bad settings"), Wr.err("child: bad settings"), Wr.err("child: bad clock"), Wr.err("child: bad clock"), Wr.err("child: bad clock"), Wr.err("child: bad clock"), Wr.err("child: bad elapsed ms"), Wr.err("child: bad poll"), Wr.err("child: bad poll"), Wr.err("child: bad poll"), Wr.err("child: bad mode"), Wr.err("child: bad fate"), Wr.err("child: bad fate"), Wr.err("child: bad id"), Wr.err("child: bad phase"), Wr.err("child: bad phase"), Wr.err("child: bad phase"), Wr.err("child: bad phase"), Wr.err("child: bad delete flag")] : List<&2, String>}

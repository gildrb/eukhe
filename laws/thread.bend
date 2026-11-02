# eukhe: the laws of area thread

import Base
import ../bend/thread.bend as Th
import ../bend/ffi_thread.bend as FTh
import ../bend/wire.bend as Wr
import ../spec/memory/thread.bend as S
import ./base.bend as LawsBase

# (M3) Each session is its own thread
# -----------------------------------
# spec/README.md M3. bend/thread.bend: a session logs only its own
# messages into its own chat (eukhe-core memory/service.rs), and a root
# turn's request (durable/optchat/request.rs) is the view lines of the
# history that scrolled out of the verbatim transcript, then the
# session's own transcript verbatim. The count of view lines kept runs as
# the compiled core by bend/ffi_thread.bend (eukhe-bend rules/thread.rs;
# asked by RenderedView::history). spec/memory/thread.bend restates the
# rule (S1-S5). Every input is free: any session, event stream, view,
# window, counts and starts.
#
# R1: a session's chat is exactly its own messages, in order (S1).
# R2: a session's request holds only its own thread's messages (S2).
# R3: the newest turns are present verbatim, as the request's end, after
#     every view line (S3).
# R4: the view keeps only the history that scrolled out of the
#     transcript: lines that start before end = T - V, and every such
#     line of an ascending view (S4, S5).
# R5: the entry answers each request Rust writes (every number and count
#     within the wire) with the model's count, reads exactly the request
#     and nothing after it, and answers any other input with the exact
#     error form `E thread: malformed request`.
# R6: the request is the spec's, whole: each kept view line carries the
#     messages of its own span, the chat's count messages from its start
#     (S6).
# R7: between two calls the request only grows at its end unless a
#     compaction ran: a call under the head its view was pinned under (no
#     compaction or reset since) sends that view, whatever a fresh render
#     would give; under a new head it sends the fresh render, pinned under
#     that head. Two calls under one head, the transcript grown by the
#     session's new messages, send the first request, then those
#     messages' turns (Rust bridge: eukhe-core durable/optchat/tests.rs
#     a_root_request_grows_only_at_its_end_until_a_compaction).

# Spec helpers
# ------------

# R5: the spelling of a request: one list of Nats, through, verbatim,
# then the starts
def sp_w_req(q: FTh.Req, rest: String) -> String:
  match q:
    case FTh.Req{t, v, xs}:
      LawsBase.wire_spell_nats(t <> v <> xs, rest)

# every number and the count of the request fit the wire
def sp_fit_req(q: FTh.Req) -> Bool:
  match q:
    case FTh.Req{+t, +v, +xs}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Nat, t <> v <> xs)), LawsBase.wire_nats_fit(t <> v <> xs))

# R5: the reply of a request: the model's count
def sp_w_reply(q: FTh.Req) -> String:
  match q:
    case FTh.Req{t, v, xs}:
      Wr.put_nat(Th.history_lines(t, v, xs), "")

# R5: the reply of a request by the spec: the count of leading starts
# below through - verbatim (S5), spelled
def sp_w_spec_reply(q: FTh.Req) -> String:
  match q:
    case FTh.Req{t, v, xs}:
      Wr.put_nat(S.lead(Nat.sub(t, v), xs), "")

# R7: the head a pin was rendered under
def sp_head(p: Th.Pin) -> Nat:
  match p:
    case Th.Pin{h, v}:
      h

# R7: the view lines of a pin
def sp_view(p: Th.Pin) -> List<&2, Th.Span>:
  match p:
    case Th.Pin{h, v}:
      v

# R7: every line of view ends within the first n messages of the chat
def sp_inside(+n: Nat, view: List<&2, Th.Span>) -> Bool:
  match view:
    case Nil{}:
      True{}
    case sp <> t:
      match sp:
        case Th.Span{st, c}:
          Bool.and(Nat.is_le(Nat.add(st, c), n), sp_inside(n, t))

# Laws: the chat (R1, R2)
# -----------------------

# LAW thread_log_chat (R1): the chat of every session over every event
# stream is the spec's: the messages that session wrote, in order
# EXCLUDES: a message of another session logged, a message of the
#   session dropped or reordered, one shared chat for every session
law thread_log_chat:
  for +s: Nat
  for +evs: List<&2, Th.Msg>
  {Th.log(s, evs) == S.chat(s, evs) : List<&2, Th.Msg>}

# LAW thread_request_own (R2): every message of a session's request (every
# turn, and every message a view line summarizes) belongs to that session
# EXCLUDES: a turn or a summarized message of another session in the
#   request, a view built over the shared stream
law thread_request_own:
  for +s: Nat
  for +evs: List<&2, Th.Msg>
  for +view: List<&2, Th.Span>
  for +w: Nat
  {S.items_own(s, Th.request(s, evs, view, w)) == True{} : Bool}

# Laws: the transcript (R3)
# -------------------------

# LAW thread_newest_verbatim (R3): the request ends with the turns of the
# chat's newest messages, in order and unchanged, after view lines only;
# the chat's messages before them are exactly end = T - V
# EXCLUDES: a newest turn dropped, summarized, changed or reordered, a
#   turn before a view line, a window off by one, an older message
#   repeated verbatim
law thread_newest_verbatim:
  for +s: Nat
  for +evs: List<&2, Th.Msg>
  for +view: List<&2, Th.Span>
  for +w: Nat
  exs hist: List<&2, Th.Item>
  exs old: List<&2, Th.Msg>
  exs new: List<&2, Th.Msg>
  {Th.request(s, evs, view, w) == List.append(&2, Th.Item, hist, S.turns(new)) : List<&2, Th.Item>} & ({S.no_turns(hist) == True{} : Bool} & ({S.chat(s, evs) == List.append(&2, Th.Msg, old, new) : List<&2, Th.Msg>} & {List.length(&2, Th.Msg, old) == S.end(S.chat(s, evs), w) : Nat}))

# Laws: the history (R4)
# ----------------------

# LAW thread_history_before (R4): every view line of a request starts
# before end = T - V: only history that scrolled out of the transcript
# EXCLUDES: a view line over messages the transcript holds verbatim kept,
#   end taken as T, a view line past end kept
law thread_history_before:
  for +s: Nat
  for +evs: List<&2, Th.Msg>
  for +view: List<&2, Th.Span>
  for +w: Nat
  {S.lines_before(S.end(S.chat(s, evs), w), Th.request(s, evs, view, w)) == True{} : Bool}

# LAW thread_history_kept (R4): over a view whose lines ascend (oldest
# first), the request's view lines are exactly the view's lines that start
# before end, in order: each kept whole
# EXCLUDES: a view line that starts before end dropped (one that straddles
#   end among them), a line kept twice or out of order
law thread_history_kept:
  for +s: Nat
  for +evs: List<&2, Th.Msg>
  for +view: List<&2, Th.Span>
  for +w: Nat
  for asc: {S.ascending(S.view_starts(view)) == True{} : Bool}
  {S.line_starts(Th.request(s, evs, view, w)) == S.before(S.end(S.chat(s, evs), w), S.view_starts(view)) : List<&2, Nat>}

# LAW thread_history_lines_spec (R4): the count of kept lines is the
# length of the longest run of leading starts below through - verbatim
# (0 when verbatim passes through)
# EXCLUDES: a start at end kept, a count that skips a start past end and
#   goes on, a subtraction that wraps
law thread_history_lines_spec:
  for +t: Nat
  for +v: Nat
  for +xs: List<&2, Nat>
  {Th.history_lines(t, v, xs) == S.lead(Nat.sub(t, v), xs) : Nat}

# LAW thread_history_lines_example (R4): anchor: 10 messages, 3 verbatim:
# end 7, lines at 0, 4, 6 kept (6 straddles end), 7 not; a window past the
# chat keeps nothing; no window keeps every line; only leading lines count
# EXCLUDES: a spec that drifts from the Rust it replaced
law thread_history_lines_example:
  {[Th.history_lines(10n, 3n, [0n, 4n, 6n, 7n]), Th.history_lines(10n, 3n, [0n, 8n]), Th.history_lines(5n, 9n, [0n, 1n]), Th.history_lines(10n, 0n, [0n, 4n, 8n]), Th.history_lines(10n, 3n, [8n, 0n])] == [3n, 1n, 0n, 3n, 0n] : List<&2, Nat>}

# LAW thread_request_example (R1-R4): anchor: two sessions interleaved;
# session 1's request over its view [0..1], [2], [3] with 3 messages
# verbatim keeps the line at 0 whole (it straddles end 1), then its own
# newest 3 messages, none of session 2's
# EXCLUDES: a request over the shared stream, a straddling line cut or
#   dropped
law thread_request_example:
  {Th.request(1n, [Th.Msg{1n, 10n}, Th.Msg{2n, 20n}, Th.Msg{1n, 11n}, Th.Msg{1n, 12n}, Th.Msg{2n, 21n}, Th.Msg{1n, 13n}], [Th.Span{0n, 2n}, Th.Span{2n, 1n}, Th.Span{3n, 1n}], 3n) == [Th.Line{0n, [Th.Msg{1n, 10n}, Th.Msg{1n, 11n}]}, Th.Turn{Th.Msg{1n, 11n}}, Th.Turn{Th.Msg{1n, 12n}}, Th.Turn{Th.Msg{1n, 13n}}] : List<&2, Th.Item>}

# Laws: the request, whole (R6)
# -----------------------------

# LAW thread_request_spec (R6): every session's request over every event
# stream, view and window is the spec's: the leading view lines that start
# before end = T - V, each Line{start, covers} with covers the chat's count
# messages from start on (List.take(List.drop(chat, start), count)), then
# the turns of the chat's messages from end on
# EXCLUDES: a view line that covers messages from another start (the
#   chat's first ones), a cut or padded cover, a kept line past end, a
#   transcript off by one
law thread_request_spec:
  for +s: Nat
  for +evs: List<&2, Th.Msg>
  for +view: List<&2, Th.Span>
  for +w: Nat
  {Th.request(s, evs, view, w) == S.request(s, evs, view, w) : List<&2, Th.Item>}

# LAW thread_request_covers_example (R6): anchor: six messages of session
# 1, view [0..1], [2..3], 2 verbatim: end 4 keeps both lines, the second
# over messages 12 and 13 (its own start), then 14 and 15 verbatim
# EXCLUDES: a line that covers the chat's first messages whatever its
#   start
law thread_request_covers_example:
  {Th.request(1n, [Th.Msg{1n, 10n}, Th.Msg{1n, 11n}, Th.Msg{1n, 12n}, Th.Msg{1n, 13n}, Th.Msg{1n, 14n}, Th.Msg{1n, 15n}], [Th.Span{0n, 2n}, Th.Span{2n, 2n}], 2n) == [Th.Line{0n, [Th.Msg{1n, 10n}, Th.Msg{1n, 11n}]}, Th.Line{2n, [Th.Msg{1n, 12n}, Th.Msg{1n, 13n}]}, Th.Turn{Th.Msg{1n, 14n}}, Th.Turn{Th.Msg{1n, 15n}}] : List<&2, Th.Item>}

# Laws: the cache prefix (R7)
# ---------------------------

# LAW thread_pin_kept (R7): a call under the head its view was pinned
# under sends that view, whatever a fresh render would give
# EXCLUDES: a view rendered again for each run (the request's prefix
#   rewritten between two calls with no compaction between them), the
#   head dropped
law thread_pin_kept:
  for +h: Nat
  for +view: List<&2, Th.Span>
  for +fresh: List<&2, Th.Span>
  {Th.pin(Th.Pin{h, view}, h, fresh) == Th.Pin{h, view} : Th.Pin}

# LAW thread_pin_moved (R7): a call under a new head (a compaction or a
# reset ran) sends the fresh render, pinned under that head
# EXCLUDES: a view kept past a compaction (the history it cut in neither
#   the view nor the transcript), the old head kept with the new view
law thread_pin_moved:
  for +p: Th.Pin
  for +h: Nat
  for +fresh: List<&2, Th.Span>
  for moved: {Nat.is_eq(sp_head(p), h) == False{} : Bool}
  {Th.pin(p, h, fresh) == Th.Pin{h, fresh} : Th.Pin}

# LAW thread_request_prefix_kept (R7): two calls of session s under one
# head h (no compaction or reset between them), the first pinning over
# the pin p, the second over the first's, with any fresh renders: when the
# first call's view covers only messages its chat holds and the window
# grows by the session's messages of the new events, the second request is
# the first, unchanged, then the turns of those messages
# EXCLUDES: a view line added, dropped or changed between the two calls, a
#   view re-rendered per run, a new turn anywhere but the end, an old turn
#   moved into the view
law thread_request_prefix_kept:
  for +s: Nat
  for +evs: List<&2, Th.Msg>
  for +more: List<&2, Th.Msg>
  for +p: Th.Pin
  for +h: Nat
  for +fresh: List<&2, Th.Span>
  for +again: List<&2, Th.Span>
  for +w: Nat
  for inside: {sp_inside(List.length(&2, Th.Msg, S.chat(s, evs)), sp_view(Th.pin(p, h, fresh))) == True{} : Bool}
  {Th.request(s, List.append(&2, Th.Msg, evs, more), sp_view(Th.pin(Th.pin(p, h, fresh), h, again)), Nat.add(w, List.length(&2, Th.Msg, S.chat(s, more)))) == List.append(&2, Th.Item, Th.request(s, evs, sp_view(Th.pin(p, h, fresh)), w), S.turns(S.chat(s, more))) : List<&2, Th.Item>}

# LAW thread_pin_example (R7): anchor: a pin under head 3 kept by a call
# under head 3, replaced by the fresh render under head 5
# EXCLUDES: a spec that drifts from the Rust it models
law thread_pin_example:
  {[Th.pin(Th.Pin{3n, [Th.Span{0n, 2n}]}, 3n, [Th.Span{0n, 4n}]), Th.pin(Th.Pin{3n, [Th.Span{0n, 2n}]}, 5n, [Th.Span{0n, 4n}])] == [Th.Pin{3n, [Th.Span{0n, 2n}]}, Th.Pin{5n, [Th.Span{0n, 4n}]}] : List<&2, Th.Pin>}

# Laws: the entry (R5)
# --------------------

# LAW thread_history_lines_is_model (R5): the entry answers every request
# Rust spells, every number within the wire, with the model's count,
# spelled
# EXCLUDES: through and verbatim swapped, a start misread, a default,
#   another reply spelling
law thread_history_lines_is_model:
  for +q: FTh.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FTh.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW thread_entry_reads (R5): the entry's decoder reads a spelled request
# back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law thread_entry_reads:
  for +q: FTh.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FTh.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FTh.Req>}

# LAW thread_entry_exact (R5): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (a list of fewer than
#   two Nats, a malformed number, input left over)
law thread_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FTh.ffi(s)) == False{} : Bool}
  exs r: FTh.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW thread_entry_refuses (R5): every error the entry answers is exactly
# `E thread: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law thread_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FTh.ffi(s)) == True{} : Bool}
  {FTh.ffi(s) == Wr.err("thread: malformed request") : String}

# LAW thread_entry_example (R5): anchor: the wire strings Rust sends and
# the replies it reads; a list of one Nat, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law thread_entry_example:
  {[FTh.ffi("5,10,3,0,4,6,"), FTh.ffi("2,5,9,"), FTh.ffi("1,10,"), FTh.ffi("2,10,3,x")] == ["3,", "0,", Wr.err("thread: malformed request"), Wr.err("thread: malformed request")] : List<&2, String>}

# LAW thread_entry_spec (R4, R5): the entry answers every request Rust
# spells, every number within the wire, with the spec's count (S5): the
# leading starts below through - verbatim, spelled
# EXCLUDES: any reply other than the spec's for a request that fits (a
#   start at end kept, a count past the first start at or after end, a
#   subtraction that wraps, another spelling)
law thread_entry_spec:
  for +q: FTh.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FTh.ffi(sp_w_req(q, "")) == sp_w_spec_reply(q) : String}

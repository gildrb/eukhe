# eukhe: the laws of area tools

import Base
import ../bend/approvals.bend as Am
import ../bend/ffi_tools.bend as FTl
import ../bend/path_policy.bend as Pp
import ../bend/tools.bend as Tl
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S7) The tool surface
# ---------------------
# the model in bend/tools.bend. Every input is free:
# any tools that join and quit, any schemas, any paths, any scripts, any
# auto set, any answers of the user.
#
# Requirements (sources: bend/tools.bend header 1-4; spec/README.md row
# A1; crates/eukhe-docs/src/url.rs `walk` and `resolve`;
# crates/eukhe-types/src/path_policy.rs; bend/approvals.bend header, the
# model of crates/eukhe-daemon/src/shell_approval.rs; the user's
# decisions of 2026-10-23 and 2026-10-27 named at their laws):
# A1: (spec/README.md) one loop: the roster is fixed at open; late tools
#     come through `dyn`.
# S7: the tool surface. (1) A session's roster never changes: tools that
#     come later join the dynamic set behind `dyn`; every request sends
#     the roster it started with (the prompt cache stays valid); a call
#     through `dyn` reaches a tool as the last join or quit of it says.
#     (2) The schema: laws/tool_surface.bend R3. (3) An internal URL's
#     path resolves under the root of its scheme: a name goes one level
#     down, `.` (or an empty segment) stays, `..` goes one level up; a
#     path that goes above its root is rejected, never clamped; the names
#     it reaches are the names no `..` cancels, deepest first (url.rs
#     `walk` reads them back root first). (4) The approval gate: G2.
# G1: one path policy for the `bash` tool and the document tools (section
#     G1 below).
# G2: a script runs step by step; a step runs unasked exactly when each of
#     its effects is one an auto set may hold (codes 0 to 6: every effect)
#     and is in the auto set; any other step asks the user and takes the
#     next answer: a yes runs it, a no or no answer left denies it; a
#     denial stops the script (the denied step and every later step do
#     not run, the script ends denied at that step's id); a step that runs
#     unasked takes no answer. A step's effects are every effect of every
#     part of it; only a part that names a secret path gives the secret
#     effect (6).
# G5: a session whose only clients are the phone gateway never waits: the
#     gateway rule refuses a step that writes a protected path (5) when
#     the auto set does not already run it, and runs every other step; the
#     default auto set holds every grantable effect.

# LAW roster_fixed: no event changes the roster: tools that join go behind `dyn`
law roster_fixed:
  for es: List<&2, Tl.Ev>
  for +s: Tl.Sess
  {Tl.Sess.roster(Tl.run(es, s)) == Tl.Sess.roster(s) : List<&2, Nat>}

# LAW roster_sent_fixed: every request of a session sends the roster it started with
law roster_sent_fixed:
  for es: List<&2, Tl.Ev>
  for +r: List<&2, Nat>
  for d: List<&2, Nat>
  {Tl.all_eq(Tl.Sess.sent(Tl.run(es, Tl.Sess{r, d, Nil{}})), r) == True{} : Bool}

# LAW dyn_reaches_joined: a tool that joins is reachable through `dyn`
law dyn_reaches_joined:
  for +s: Tl.Sess
  for +t: Nat
  {Tl.dyn_call(Tl.step(s, Tl.Join{t}), t) == True{} : Bool}

# LAW dyn_drops_quit: a tool that quits is not reachable through `dyn`
law dyn_drops_quit:
  for +s: Tl.Sess
  for +t: Nat
  {Tl.dyn_call(Tl.step(s, Tl.Quit{t}), t) == False{} : Bool}

# (S7, 1) The roster over a history
# ---------------------------------
# Every input is free: any session, any events.

# how many requests (Turn) es holds
def tr_turns(es: List<&2, Tl.Ev>) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case Tl.Join{t}:
          tr_turns(rest)
        case Tl.Quit{t}:
          tr_turns(rest)
        case Tl.Turn{}:
          1n+tr_turns(rest)

# n copies of the roster r
def tr_copies(n: Nat, +r: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      r <> tr_copies(m, r)

# what an event that names tool t (b) says of t: v
def tr_hit(b: Bool, v: Bool) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      None{}

# what one event says of tool t: a join of t that it is reached, a quit
# of t that it is not, any other event nothing
def tr_says(e: Tl.Ev, +t: Nat) -> Maybe<&2, Bool>:
  match e:
    case Tl.Join{u}:
      tr_hit(Nat.is_eq(u, t), True{})
    case Tl.Quit{u}:
      tr_hit(Nat.is_eq(u, t), False{})
    case Tl.Turn{}:
      None{}

# what a later event said, else what this one says
def tr_later(later: Maybe<&2, Bool>, here: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match later:
    case Some{v}:
      Some{v}
    case None{}:
      here

# what the last event of es that joins or quits t says of t
def tr_last(es: List<&2, Tl.Ev>, +t: Nat) -> Maybe<&2, Bool>:
  match es:
    case Nil{}:
      None{}
    case e <> rest:
      tr_later(tr_last(rest, t), tr_says(e, t))

# what m says, else b
def tr_or(m: Maybe<&2, Bool>, b: Bool) -> Bool:
  match m:
    case Some{v}:
      v
    case None{}:
      b

# LAW roster_sent_per_request (A1, S7): after any events from any session, the rosters sent are one copy of the session's roster per request (Turn) among the events, in front of the rosters sent before it; joins and quits record nothing
# EXCLUDES: a run that ignores its events (which roster_fixed and
#   roster_sent_fixed let pass), a request that records no roster, two, or
#   the dynamic tools, a join or a quit that records one, a record lost
law roster_sent_per_request:
  for es: List<&2, Tl.Ev>
  for +s: Tl.Sess
  {Tl.Sess.sent(Tl.run(es, s)) == List.append(&2, List<&2, Nat>, tr_copies(tr_turns(es), Tl.Sess.roster(s)), Tl.Sess.sent(s)) : List<&2, List<&2, Nat>>}

# LAW dyn_reach_follows_last_event (A1, S7): after any events from any session, a call through `dyn` reaches tool t exactly as the last join or quit of t among the events says (a join: reached; a quit: not), and as before the events when none joins or quits t
# EXCLUDES: a run that ignores, skips, repeats or reorders its events, a
#   join or a quit that changes whether another tool is reached, a request
#   that changes the dynamic tools
law dyn_reach_follows_last_event:
  for es: List<&2, Tl.Ev>
  for +s: Tl.Sess
  for +t: Nat
  {Tl.dyn_call(Tl.run(es, s), t) == tr_or(tr_last(es, t), Tl.dyn_call(s, t)) : Bool}

# LAW schema_has_intent: every schema the harness sends has the intent parameter
law schema_has_intent:
  for s: Tl.Schema
  {Tl.elem(Tl.Schema.params(Tl.build(s)), Tl.intent()) == True{} : Bool}

# LAW schema_versioned: every schema the harness sends has a version of at least 1
law schema_versioned:
  for s: Tl.Schema
  {Nat.is_le(1n, Tl.Schema.version(Tl.build(s))) == True{} : Bool}

# LAW schema_keeps_params: the harness keeps every parameter a tool declares
law schema_keeps_params:
  for +s: Tl.Schema
  for +x: Nat
  for has: {Tl.elem(Tl.Schema.params(s), x) == True{} : Bool}
  {Tl.elem(Tl.Schema.params(Tl.build(s)), x) == True{} : Bool}

# LAW schema_build_idempotent: building a built schema changes nothing
law schema_build_idempotent:
  for +s: Tl.Schema
  {Tl.build(Tl.build(s)) == Tl.build(s) : Tl.Schema}

# LAW path_rejects_escape: a path that goes above its root is rejected, never clamped
law path_rejects_escape:
  for +segs: List<&2, Tl.Seg>
  for out: {Tl.stays(segs, 0n) == False{} : Bool}
  {Tl.resolve(segs) == None{} : Maybe<&2, List<&2, Nat>>}

# LAW path_resolves_inside: a path that stays under its root resolves
law path_resolves_inside:
  for +segs: List<&2, Tl.Seg>
  for inside: {Tl.stays(segs, 0n) == True{} : Bool}
  {Maybe.is_some(&2, List<&2, Nat>, Tl.resolve(segs)) == True{} : Bool}

# Which names a path reaches (S7.6: `..` goes up one segment; `.` and an
# empty segment do not move; a path above its root is refused, never
# clamped). Together the four laws below decide Tl.resolve on every path:
# dropping each `.` and each name followed by `..` leaves a path of names
# only (path_names_plain), or one that begins with `..` (path_up_at_root,
# where the path before it is empty).

# the path of the names ns, in order
def tools_name_path(ns: List<&2, Nat>) -> List<&2, Tl.Seg>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> rest:
      Tl.Name{n} <> tools_name_path(rest)

# LAW path_up_cancels: a name followed by `..`, anywhere in a path, changes nothing: the path
# resolves as without the two
# EXCLUDES: `..` that keeps the name, goes two levels up, or drops the
#   root-most name instead of the deepest
law path_up_cancels:
  for +pre: List<&2, Tl.Seg>
  for +n: Nat
  for +post: List<&2, Tl.Seg>
  {Tl.resolve(List.append(&2, Tl.Seg, pre, Tl.Name{n} <> Tl.Up{} <> post)) == Tl.resolve(List.append(&2, Tl.Seg, pre, post)) : Maybe<&2, List<&2, Nat>>}

# LAW path_here_drops: a `.`, anywhere in a path, changes nothing: the path resolves as without it
# EXCLUDES: `.` read as a name, as `..`, or as the end of the path
law path_here_drops:
  for +pre: List<&2, Tl.Seg>
  for +post: List<&2, Tl.Seg>
  {Tl.resolve(List.append(&2, Tl.Seg, pre, Tl.Here{} <> post)) == Tl.resolve(List.append(&2, Tl.Seg, pre, post)) : Maybe<&2, List<&2, Nat>>}

# LAW path_names_plain: a path of names only reaches those names, deepest (last) first
# EXCLUDES: names root first, a name dropped, repeated or changed
law path_names_plain:
  for +ns: List<&2, Nat>
  {Tl.resolve(tools_name_path(ns)) == Some{List.reverse(&2, Nat, ns)} : Maybe<&2, List<&2, Nat>>}

# LAW path_up_at_root: `..` where a path has reached its root (the segments before it resolve to
# the root) goes above it: the path is refused, whatever follows
# EXCLUDES: `..` at the root clamped to the root, skipped, or read as a
#   name; a path that goes above its root answered because later names
#   bring it back under
law path_up_at_root:
  for +pre: List<&2, Tl.Seg>
  for +post: List<&2, Tl.Seg>
  for root: {Tl.resolve(pre) == Some{Nil{}} : Maybe<&2, List<&2, Nat>>}
  {Tl.resolve(List.append(&2, Tl.Seg, pre, Tl.Up{} <> post)) == None{} : Maybe<&2, List<&2, Nat>>}

# LAW tools_ffi_request_round_trip (compiled core, S7): the path entry's decoder (FTl.get_req, bend/ffi_tools.bend) reads back the segments of a path as the entry's own encoder FTl.put_req writes them (every count and code of FTl.codes within the wire), and leaves what follows untouched; the spelling Rust writes is pinned by tools_ffi_answers_spelled and tools_ffi_tags_example, not here
# EXCLUDES: a decoder that misreads, drops, reorders or shifts a segment
#   the encoder wrote, or eats the input after the request (a code drift
#   both Bend sides share passes this law)
law tools_ffi_request_round_trip:
  for +gs: List<&2, Tl.Seg>
  for +rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FTl.codes(gs))), LawsBase.wire_nats_fit(FTl.codes(gs))) == True{} : Bool}
  {FTl.get_req(FTl.put_req(gs, rest)) == Wr.Got{gs, rest} : Wr.Dec<List<&2, Tl.Seg>>}

# The path entry, spelled
# -----------------------
# The round trip above reads and writes through the entry's own encoder
# (FTl.put_req, FTl.codes): a segment code drift both sides share (Up and
# Here swapped, a name offset) passes it. The laws below spell the request
# and the reply with the wire primitives as Rust writes and reads them
# (crates/eukhe-docs/src/url.rs `resolve`): the segment codes as a wire
# list of Nats (0 Up `..`, 1 Here `.` or empty, 2 + n the name at segment
# index n); the reply to a path is the model's resolution (Tl.resolve,
# whose names the path laws above and path_resolve_spec pin): 0 when the
# path goes above its root, else 1 then the names it reaches, deepest
# first, as a wire list of Nats.

# the code Rust writes for a segment
def tools_seg_code(g: Tl.Seg) -> Nat:
  match g:
    case Tl.Up{}:
      0n
    case Tl.Here{}:
      1n
    case Tl.Name{n}:
      2n+n

def tools_seg_codes(gs: List<&2, Tl.Seg>) -> List<&2, Nat>:
  match gs:
    case Nil{}:
      Nil{}
    case g <> rest:
      tools_seg_code(g) <> tools_seg_codes(rest)

# a request as Rust spells it: the segment codes, then rest
def tools_spell_req(gs: List<&2, Tl.Seg>, rest: String) -> String:
  LawsBase.wire_spell_nats(tools_seg_codes(gs), rest)

# the count and every code of a request fit the wire
def tools_req_fits(gs: List<&2, Tl.Seg>) -> Bool:
  +cs = tools_seg_codes(gs)
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs))

# the reply as Rust reads it: 0 above the root, else 1 then the names
def tools_spell_names(m: Maybe<&2, List<&2, Nat>>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{xs}:
      Wr.put_nat(1n, LawsBase.wire_spell_nats(xs, ""))

# the spelled reply to a request: the model's resolution of the path
def tools_spell_answer(gs: List<&2, Tl.Seg>) -> String:
  tools_spell_names(Tl.resolve(gs))

# LAW tools_ffi_answers_spelled: a path spelled as Rust writes it, every count and code within
# the wire, is answered as Rust reads it: 0 when the model's resolution
# (Tl.resolve) goes above the root, else 1 then the names it reaches,
# deepest first
# EXCLUDES: a request or reply tag drift both sides of the Bend entry share
#   (Up and Here swapped, a name offset other than 2, the reply tags
#   swapped), names spelled root first, an entry that answers another walk
#   than the model's (a path clamped at its root)
law tools_ffi_answers_spelled:
  for +gs: List<&2, Tl.Seg>
  for fits: {tools_req_fits(gs) == True{} : Bool}
  {FTl.ffi(tools_spell_req(gs, "")) == tools_spell_answer(gs) : String}

# LAW tools_ffi_left_over_spelled: a spelled path that fits, followed by any more input,
# answers the error form "tools: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request, or
#   answered with another error text
law tools_ffi_left_over_spelled:
  for +gs: List<&2, Tl.Seg>
  for fits: {tools_req_fits(gs) == True{} : Bool}
  for +c: Char
  for +t: String
  {FTl.ffi(tools_spell_req(gs, SCon{c, t})) == Wr.err("tools: input left over") : String}

# LAW tools_ffi_reads_only_requests: an answer that is not the error form answers a path: the
# input is exactly the spelling of a path whose count and codes fit the
# wire, and the answer is the spelled names it reaches
# EXCLUDES: a decoder that accepts a short list or input left over and
#   answers it anyway (a default instead of the error form)
law tools_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FTl.ffi(s)) == False{} : Bool}
  exs gs: List<&2, Tl.Seg>
  {(s, (tools_req_fits(gs), FTl.ffi(s))) == (tools_spell_req(gs, ""), (True{}, tools_spell_answer(gs))) : String & (Bool & String)}

# LAW tools_ffi_malformed_unless_request: every answer but the error form "tools: malformed
# request" comes from an input that begins with a spelled path that fits
# (with tools_ffi_answers_spelled and tools_ffi_left_over_spelled this
# pins the entry's answer to every input)
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law tools_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FTl.ffi(s), Wr.err("tools: malformed request")) == False{} : Bool}
  exs gs: List<&2, Tl.Seg>
  exs rest: String
  {(s, tools_req_fits(gs)) == (tools_spell_req(gs, rest), True{}) : String & Bool}

# LAW tools_ffi_tags_example: anchor: the bytes Rust sends and reads: `a/../b` (codes 2, 0,
# 4) reaches b (1 then [2]); `..` goes above the root (0); `.` and the
# empty path reach the root (1 then []); `a/b` reaches [1, 0], deepest
# first; `a/../..` goes above the root; a short list and empty input are
# malformed; input after the path is left over
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust does
#   not (segment codes, the reply's 0/1), names root first
law tools_ffi_tags_example:
  {[FTl.ffi("3,2,0,4,"), FTl.ffi("1,0,"), FTl.ffi("1,1,"), FTl.ffi("0,"), FTl.ffi("2,2,3,"), FTl.ffi("3,2,0,0,"), FTl.ffi("2,2,"), FTl.ffi(""), FTl.ffi("1,1,x")] == ["1,1,2,", "0,", "1,0,", "1,0,", "1,2,1,0,", "0,", Wr.err("tools: malformed request"), Wr.err("tools: malformed request"), Wr.err("tools: input left over")] : List<&2, String>}

# (S7, 3) The path entry, against a spec
# --------------------------------------
# An internal URL's path is a list of segments under the root of its
# scheme: a name goes one level down, `.` (or an empty segment) stays,
# `..` goes one level up; a path that goes above its root is rejected,
# never clamped. Read from its end, each `..` cancels the nearest name
# before it that no other `..` cancels; the names left are the names the
# path reaches; a `..` that no name before it is left to cancel goes above
# the root. Every input is free: any segments, any text.

# a name met with u uncancelled `..` after it: it cancels one of them
def tp_ups.name(u: Nat) -> Nat:
  match u:
    case 0n:
      0n
    case 1n+v:
      v

# the `..` of segs that no name of segs cancels
def tp_ups(segs: List<&2, Tl.Seg>) -> Nat:
  match segs:
    case Nil{}:
      0n
    case g <> rest:
      match g:
        case Tl.Name{n}:
          tp_ups.name(tp_ups(rest))
        case Tl.Up{}:
          1n+tp_ups(rest)
        case Tl.Here{}:
          tp_ups(rest)

# the name n before the names ns that stay, with u uncancelled `..` after
# it: it stays (the shallowest, last) when no `..` is left to cancel it
def tp_names.name(n: Nat, u: Nat, ns: List<&2, Nat>) -> List<&2, Nat>:
  match u:
    case 0n:
      List.append(&2, Nat, ns, [n])
    case 1n+v:
      ns

# the names of segs that no `..` cancels, deepest (last) first
def tp_names(segs: List<&2, Tl.Seg>) -> List<&2, Nat>:
  match segs:
    case Nil{}:
      Nil{}
    case g <> +rest:
      match g:
        case Tl.Name{n}:
          tp_names.name(n, tp_ups(rest), tp_names(rest))
        case Tl.Up{}:
          tp_names(rest)
        case Tl.Here{}:
          tp_names(rest)

def tp_resolve.at(u: Nat, ns: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match u:
    case 0n:
      Some{ns}
    case 1n+v:
      None{}

# the names the path reaches, deepest first; None when a `..` goes above
# the root
def tp_resolve(+segs: List<&2, Tl.Seg>) -> Maybe<&2, List<&2, Nat>>:
  tp_resolve.at(tp_ups(segs), tp_names(segs))

# the segment a request code names (the grammar of bend/ffi_tools.bend):
# 0 `..`, 1 `.`, 2 + n the name n
def tp_seg(c: Nat) -> Tl.Seg:
  match c:
    case 0n:
      Tl.Up{}
    case 1n:
      Tl.Here{}
    case 2n+n:
      Tl.Name{n}

def tp_segs(cs: List<&2, Nat>) -> List<&2, Tl.Seg>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      tp_seg(c) <> tp_segs(rest)

# the reply: 0 (above the root), or 1 then the names
def tp_reply(m: Maybe<&2, List<&2, Nat>>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{ns}:
      Wr.put_nat(1n, Wr.put_list(~Nat, ~Wr.put_nat, ns, ""))

# the error form of an input that is no request
def tp_malformed() -> String:
  SCon{'E', SCon{' ', "tools: malformed request"}}

# the error form of a request followed by more input
def tp_left_over() -> String:
  SCon{'E', SCon{' ', "tools: input left over"}}

def tp_entry.end(whole: Bool, cs: List<&2, Nat>) -> String:
  match whole:
    case True{}:
      tp_reply(tp_resolve(tp_segs(cs)))
    case False{}:
      tp_left_over()

def tp_entry.read(r: Wr.Dec<List<&2, Nat>>) -> String:
  match r:
    case Wr.Got{cs, s}:
      tp_entry.end(Wr.end(s), cs)
    case Wr.Bad{}:
      tp_malformed()

# the reply of the path entry to the input s: the request is a list of
# codes read with the wire primitives
def tp_entry(s: String) -> String:
  tp_entry.read(Wr.get_list(~Nat, ~Wr.get_nat, s))

# LAW path_resolve_spec (S7 3): every path resolves as the spec reads
# it: each `..` cancels the nearest name before it left to cancel; the
# names no `..` cancels are the names reached, deepest first; a `..` with
# no name left to cancel goes above the root, and the path is rejected
# EXCLUDES: a path clamped at its root, a `..` that cancels another name
#   or none, names reordered, dropped, repeated or invented, `.` taken as
#   a name or as `..`
law path_resolve_spec:
  for +segs: List<&2, Tl.Seg>
  {Tl.resolve(segs) == tp_resolve(segs) : Maybe<&2, List<&2, Nat>>}

# LAW tools_ffi_exact (compiled core): on every input the path entry
# answers exactly the spec's reply: a whole request (a list of codes read
# with the wire's reader, nothing left) gets 0 when its path goes above
# its root, else 1 then the names it reaches; a request followed by more
# input gets exactly the error form "tools: input left over"; any other
# input exactly the error form "tools: malformed request"
# EXCLUDES: a code read as another segment, a reply in another spelling,
#   input left over ignored, a default for malformed input, another error
#   text
law tools_ffi_exact:
  for +s: String
  {FTl.ffi(s) == tp_entry(s) : String}

# LAW tools_ffi_example (compiled core): anchor: the bytes of requests and
# their replies: names 0 and 1, `..`, name 2 reach 2 under 0; `..` at the
# root is rejected; the empty path reaches the root; input left over; a
# list shorter than its count
# EXCLUDES: another spelling of a request or a reply
law tools_ffi_example:
  {[FTl.ffi("4,2,3,0,4,"), FTl.ffi("2,0,2,"), FTl.ffi("0,"), FTl.ffi("1,1,x"), FTl.ffi("1,")] == ["1,2,2,0,", "0,", "1,0,", tp_left_over(), tp_malformed()] : List<&2, String>}

# LAW gate_prefix: the steps that ran are the script's first steps, in order
law gate_prefix:
  for +ss: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for ans: List<&2, Bool>
  {Tl.prefix(Tl.Ran.steps(Tl.exec(ss, auto, ans)), ss) == True{} : Bool}

# LAW gate_needs_yes: no more gated steps run than the user approved
law gate_needs_yes:
  for +ss: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for +ans: List<&2, Bool>
  {Nat.is_le(Tl.gated(Tl.Ran.steps(Tl.exec(ss, auto, ans)), auto), Tl.yeses(ans)) == True{} : Bool}

# LAW gate_deny_stops: a denial stops the script at the denied step: the steps before it
# ran, it and every later step did not
law gate_deny_stops:
  for +pre: List<&2, Tl.Step>
  for +s: Tl.Step
  for +post: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for ans: List<&2, Bool>
  for free: {Tl.gated(pre, auto) == 0n : Nat}
  for held: {Tl.auto.at(auto, s) == False{} : Bool}
  {Tl.exec(List.append(&2, Tl.Step, pre, s <> post), auto, False{} <> ans) == Tl.Ran{pre, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}

# LAW gate_finish_runs_all: a script that finished ran every step
law gate_finish_runs_all:
  for +ss: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for +ans: List<&2, Bool>
  for fin: {Tl.End.finished(Tl.Ran.end(Tl.exec(ss, auto, ans))) == True{} : Bool}
  {Tl.Ran.steps(Tl.exec(ss, auto, ans)) == ss : List<&2, Tl.Step>}

# (G2, 4) The gate, by its parts
# ------------------------------
# A script is free: steps that run unasked (pre), then a step that asks
# (s), then any steps (post). With the laws above (gate_prefix,
# gate_deny_stops) they pin how every script runs: split it at its first
# step that asks. Every input is free: any steps, any auto set, any
# answers.

# c is in xs
def tg_in(xs: List<&2, Nat>, +c: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, c), tg_in(rest, c))

# each effect of effs is one an auto set may hold (codes 0 to 6) and is in
# auto
def tg_unasked(effs: List<&2, Nat>, +auto: List<&2, Nat>) -> Bool:
  match effs:
    case Nil{}:
      True{}
    case +c <> rest:
      Bool.and(Bool.and(Nat.is_lt(c, 7n), tg_in(auto, c)), tg_unasked(rest, auto))

# step s runs unasked (G2)
def tg_free(s: Tl.Step, +auto: List<&2, Nat>) -> Bool:
  match s:
    case Tl.Step{i, f}:
      tg_unasked(f, auto)

# every step of ss runs unasked
def tg_all_free(ss: List<&2, Tl.Step>, +auto: List<&2, Nat>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case s <> rest:
      Bool.and(tg_free(s, auto), tg_all_free(rest, auto))

# the steps xs ran, then the rest ran as r
def tg_after(xs: List<&2, Tl.Step>, r: Tl.Ran) -> Tl.Ran:
  match r:
    case Tl.Ran{ss, e}:
      Tl.Ran{List.append(&2, Tl.Step, xs, ss), e}

# LAW gate_unasked_runs_all (G2): a script whose every step runs unasked (each effect one an auto set may hold, codes 0 to 6, and in the auto set) runs every step and finishes, whatever the user's answers: none is asked for
# EXCLUDES: a step asked although its effects are in the auto set (an
#   effect 4, 5 or 6 taken as one no auto set may hold), a free step that
#   takes an answer (and is denied when none is left), a script that stops
#   early
law gate_unasked_runs_all:
  for +ss: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for ans: List<&2, Bool>
  for free: {tg_all_free(ss, auto) == True{} : Bool}
  {Tl.exec(ss, auto, ans) == Tl.Ran{ss, Tl.Finished{}} : Tl.Ran}

# LAW gate_yes_runs_held (G2): steps that run unasked, then a step that asks (an effect not in the auto set, or one no auto set may hold) answered yes: they and it run, that one answer taken, and the script goes on from the next step with the answers after it
# EXCLUDES: a yes taken as a denial, a held step run unasked or with an
#   answer it did not get, an answer taken by a free step, answers used
#   out of order, a step lost or repeated
law gate_yes_runs_held:
  for +pre: List<&2, Tl.Step>
  for +s: Tl.Step
  for +post: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for ans: List<&2, Bool>
  for free: {tg_all_free(pre, auto) == True{} : Bool}
  for held: {tg_free(s, auto) == False{} : Bool}
  {Tl.exec(List.append(&2, Tl.Step, pre, s <> post), auto, True{} <> ans) == tg_after(List.append(&2, Tl.Step, pre, [s]), Tl.exec(post, auto, ans)) : Tl.Ran}

# LAW gate_held_denied_without_yes (G2): steps that run unasked, then a step that asks, with no answer left or answered no: the script stops there, the steps before it ran, it and every later step did not, and it ends denied at that step's id
# EXCLUDES: a missing answer taken as a yes, a held step run unasked (an
#   effect 7 or more in the auto set taken as grantable), a denial that
#   runs a later step, drops the steps before it or ends at another id
law gate_held_denied_without_yes:
  for +pre: List<&2, Tl.Step>
  for +s: Tl.Step
  for +post: List<&2, Tl.Step>
  for +auto: List<&2, Nat>
  for ans: List<&2, Bool>
  for +free: {tg_all_free(pre, auto) == True{} : Bool}
  for +held: {tg_free(s, auto) == False{} : Bool}
  {Tl.exec(List.append(&2, Tl.Step, pre, s <> post), auto, Nil{}) == Tl.Ran{pre, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran} & {Tl.exec(List.append(&2, Tl.Step, pre, s <> post), auto, False{} <> ans) == Tl.Ran{pre, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}

# ---- path_policy ----

# LAWS (G1): the path policy. Each law is an open claim about the model
# in bend/path_policy.bend; PROOF.bend proves them (as Tools.<law>) with the
# lemmas of proof/path_policy/.

# (G1) Path policy
# ----------------
# One policy for the `bash` tool and the document
# tools (crates/eukhe-types/src/path_policy.rs). A path is a list of
# segments from `/`; the symlinks are free (any location, any target,
# from `/` or from the link's directory, loops included); the policy is
# free (any roots, protected rules and secret entries). An access is
# judged on the real path; its effects run unasked only when the auto
# set (`shell.autoEffects`, any value) allows each of them. The user's
# answer is free: yes, no, or none (no client answered).

# LAW gate_inside_write_runs: with writes in the auto set, a write Inside runs without a
# question
law gate_inside_write_runs:
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for w: {Tl.elem(auto, 1n) == True{} : Bool}
  {Pp.runs(Pp.Inside{}, Pp.Wr{}, auto, ans) == True{} : Bool}

# ---- shell_classification ----

# shell_classification: the laws of section G2 (PROOF.bend proves them
# as Tools.<law>).

# (G2) Shell classification
# -------------------------
# the gate model of bend/tools.bend part 4. A step has a
# set of effects (codes: 0 read, 1 write, 2 exec, 3 net, 4 outside, 5
# protected, 6 secret): every effect of every part of it (its command,
# each redirection, each path it names; every command an external script
# holds). A part names a path that is or holds a secret, or not; only such
# a part gives the secret effect. Every input is free: any parts, any
# effects, any auto set (codes 4 to 6 in it too), any answers of the user.

# LAW step_holds_every_part: a step made of parts has every effect of every part
law step_holds_every_part:
  for +pre: List<&2, List<&2, Nat>>
  for +p: List<&2, Nat>
  for +post: List<&2, List<&2, Nat>>
  for +c: Nat
  for has: {Tl.elem(p, c) == True{} : Bool}
  {Tl.elem(Tl.join(List.append(&2, List<&2, Nat>, pre, p <> post)), c) == True{} : Bool}

# LAW secret_needs_a_secret_path: a step has the secret effect (6) only when one of its parts names
# a path that is or holds a secret (an operand, an option value, a
# redirection target, the working directory of a command that reads it
# because it names no path): a step whose parts name none has no secret
# effect, whatever else they hold
law secret_needs_a_secret_path:
  for +ps: List<&2, Tl.Part>
  for has: {Tl.elem(Tl.join(Tl.parts.effs(ps)), 6n) == True{} : Bool}
  {Tl.parts.secret(ps) == True{} : Bool}

# LAW secret_path_gives_secret: a part that names a path that is or holds a secret gives its step
# the secret effect (6)
law secret_path_gives_secret:
  for +pre: List<&2, Tl.Part>
  for +p: Tl.Part
  for +post: List<&2, Tl.Part>
  for named: {Tl.Part.secret(p) == True{} : Bool}
  {Tl.elem(Tl.join(Tl.parts.effs(List.append(&2, Tl.Part, pre, p <> post))), 6n) == True{} : Bool}

# LAW auto_needs_every_effect: a step with one effect that is not in the auto set, or that no auto
# set may hold, does not run without a question
law auto_needs_every_effect:
  for +s: Tl.Step
  for +auto: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(Tl.Step.effs(s), c) == True{} : Bool}
  for out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}
  {Tl.auto.at(auto, s) == False{} : Bool}

# LAW composed_needs_every_part: a step made of parts runs without a question only when every effect
# of every part is within the auto set
law composed_needs_every_part:
  for +i: Nat
  for +pre: List<&2, List<&2, Nat>>
  for +p: List<&2, Nat>
  for +post: List<&2, List<&2, Nat>>
  for +auto: List<&2, Nat>
  for +c: Nat
  for has: {Tl.elem(p, c) == True{} : Bool}
  for out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}
  {Tl.auto.at(auto, Tl.Step{i, Tl.join(List.append(&2, List<&2, Nat>, pre, p <> post))}) == False{} : Bool}

# (G5) A session that runs only from the phone gateway never waits
# -----------------------------------------------------------------
# The phone gateway shows no question. A step is guarded when it writes a
# protected path (effect 5: eukhe's own config and credentials, a .git or
# .eukhe dir, a PATH dir); the rule refuses it when the auto set does not
# already run it, and runs every other step.

# the step runs, as the gate decides it
def gw_fate_runs(f: Am.Fate) -> Bool:
  match f:
    case Am.Runs{}:
      True{}
    case Am.Denied{}:
      False{}
    case Am.Unheard{}:
      False{}
    case Am.GatewayRefused{}:
      False{}

def gw_runs(g: Am.Gated) -> Bool:
  match g:
    case Am.Unasked{}:
      True{}
    case Am.Routed{o, f}:
      gw_fate_runs(f)

# LAW gateway_runs_unprotected (G5): in a session whose only clients are the phone gateway, with any auto set and any sessions above it, a step that writes no protected path (5) runs: unasked when its effects are within the auto set, else by the gateway rule, a secret access (6) and a write outside the workspace (4) included
# EXCLUDES: a phone-only session that waits on a question, refuses or
#   leaves unanswered a step that writes no protected path (a secret
#   access refused, a guard on another effect)
law gateway_runs_unprotected:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for not_protected: {tg_in(es, 5n) == False{} : Bool}
  for +above: List<&2, Am.Desk>
  {gw_runs(Am.gate(auto, es, Am.Phone{} <> above)) == True{} : Bool}

# (G5) The default auto set
# --------------------------------------------------
# A step runs unasked when its effects are within the auto set
# (`shell.autoEffects`, bend/tools.bend `within`). The test
# crates/eukhe-core/src/durable/shell/tests.rs
# `the_default_auto_set_is_its_model` reads the real auto set of a
# session with no settings and compares it with the core's
# `default_auto` (the call of bend/ffi_approvals.bend).

# LAW default_auto_is_grantable (changed 2026-10-27 by the user: secrets
# never ask again): the auto set of a session whose user sets none holds
# exactly the grantable effects: every effect
law default_auto_is_grantable:
  for +c: Nat
  {Tl.elem(Am.default_auto(), c) == Tl.grantable(c) : Bool}

# LAW outside_runs_only_by_the_gateway (changed 2026-10-23 by the user: no prompts, like omp): in a
# session whose only clients are the phone gateway and whose auto set
# lacks outside (4), a write outside the workspace that is not protected
# and touches no secret runs, and only by the gateway rule
law outside_runs_only_by_the_gateway:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for outside: {Tl.elem(es, 4n) == True{} : Bool}
  for off: {Tl.elem(auto, 4n) == False{} : Bool}
  for not_protected: {Tl.elem(es, 5n) == False{} : Bool}
  for not_secret: {Tl.elem(es, 6n) == False{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.Runs{}} : Am.Gated}

# LAW guarded_refused_from_the_phone (changed 2026-10-27 by the user:
# secrets never ask again): and there a step that writes a protected path
# (effect 5) is refused at once, when the auto set does not already run it
law guarded_refused_from_the_phone:
  for +auto: List<&2, Nat>
  for +es: List<&2, Nat>
  for protected: {Tl.elem(es, 5n) == True{} : Bool}
  for off: {Tl.elem(auto, 5n) == False{} : Bool}
  for +above: List<&2, Am.Desk>
  {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.GatewayRefused{}} : Am.Gated}

# ys, with y in front unless y is the tool that quits (hit)
def tr_keep(hit: Bool, y: Nat, ys: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      ys
    case False{}:
      y <> ys

# the dynamic tools ds without tool t
def tr_drop(ds: List<&2, Nat>, +t: Nat) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case +y <> rest:
      tr_keep(Nat.is_eq(y, t), y, tr_drop(rest, t))

# the session after event e
def tr_step(s: Tl.Sess, e: Tl.Ev) -> Tl.Sess:
  match s:
    case Tl.Sess{+r, d, x}:
      match e:
        case Tl.Join{t}:
          Tl.Sess{r, t <> d, x}
        case Tl.Quit{t}:
          Tl.Sess{r, tr_drop(d, t), x}
        case Tl.Turn{}:
          Tl.Sess{r, d, r <> x}

# LAW roster_step_spec (A1): every event moves a session exactly as the
# spec states: a join puts the tool in front of the dynamic tools, a quit
# removes every copy of it and keeps the others in order, a request
# records the roster in front of the rosters sent; the roster never
# changes
# EXCLUDES: a join that adds nothing, another tool or a copy too many; a
#   quit that keeps a copy, drops another tool too (or every tool) or
#   reorders the rest; a request that records another roster or none; a
#   step that changes the roster
law roster_step_spec:
  for +s: Tl.Sess
  for +e: Tl.Ev
  {Tl.step(s, e) == tr_step(s, e) : Tl.Sess}

# the session after the events es from s: one step at a time, in order
def tr_run(es: List<&2, Tl.Ev>, s: Tl.Sess) -> Tl.Sess:
  match es:
    case Nil{}:
      s
    case e <> rest:
      tr_run(rest, tr_step(s, e))

# LAW roster_run_spec (A1): a session after events is the spec's step
# taken once per event, in order, from where the session started
# EXCLUDES: a run that ignores its events (`run(es, s) = s`, which
#   roster_fixed and roster_sent_fixed let pass), skips, repeats or
#   reorders them, or steps another way than the step
law roster_run_spec:
  for +es: List<&2, Tl.Ev>
  for +s: Tl.Sess
  {Tl.run(es, s) == tr_run(es, s) : Tl.Sess}

# eukhe: the laws of area compactor
#
# The compactor writes the chat memory's lines (spec/README.md M2: a
# compactor line fits its budget). The model is bend/compactor.bend (its
# headings H1, H2, H2.1), the entry bend/ffi_compactor.bend, the Rust
# caller crates/eukhe-bend/src/rules/compactor.rs. No outside source
# states a compactor, so these requirements come from the model's header
# and the Rust docs.
#
# H1 A compactor call (a line of a node: its input, at most `tries` model
# calls, `node` bytes) always ends, with a line that fits. A reply is
# free: any text, empty, thinking only, an error, missing.
# R1: a line makes at most `tries` model calls (line_calls_at_most_tries)
# R2: a provider error, or no reply, fails the call, at any try (line_error_fails)
# R3: an empty or thinking-only reply is a try that ends the call with the best reply so far cut to node bytes, else the input cut (line_empty_is_a_try)
# R4: a reply of 1 to node bytes ends the call: it is the line, whole; so the line is the first reply that fits (line_takes_fit, line_takes_first_fit)
# R5: a reply past the node asks again only while it is shorter than the best reply so far: a follow-up not shorter ends the call with the best reply cut (line_stops_when_not_shorter)
# R6: with no try left the line is the best (last, so shortest) reply cut, else the input cut (line_out_of_tries)
# R7: a cut is the longest start of the text within the room, never inside a character (cut_is_a_start_within, cut_longest)
# R8: with an input and a node of at least 4 bytes, a line that does not fail has 1 to node bytes (line_fits)
# R9: the shipped decision, one reply at a time (line.open, line.step), is `line`, and each end names the text Rust cuts: the reply just read, the best reply, or the input (line_steps, open_end_names_its_text, step_end_names_its_text)
# H2 A turn never waits forever for the memory.
# R10: a pending line after its calls: a saved line builds it, and so does the failure with no failures left; any other failure counts down by exactly one; a disk error and a stop change nothing; a built line stays built (pend_run_counts, fail_cap_builds)
# R11: an outcome changes only the line its call is for, and the view keeps its lines (settle_run_lines)
# R12: an outcome counts when its line is pending and its call saved the line or failed; the counts of outcomes in order add up (settle_hits_one, settle_hits_split)
# R13: each counted outcome lowers the measure, so after as many counted outcomes as the measure at the start every line is built; at the start the measure is the failure cap times the lines not built (settle_falls, settle_bounded, settle_reached, settle_start)
# H2.1 Need first.
# R14: while a turn waits, the queue starts only view lines not built, and the wait stops every call it does not need and none it needs (need_first, need_first_due, need_first_running, wait_keeps_needed)
# M2 The entry.
# R15: each request Rust spells gets the model's decision on it (compactor_ffi_open, compactor_ffi_step, compactor_ffi_after); a node Rust saturates at the wire bound changes no decision (line_step_node_beyond_reply)
# R16: every other input gets the error form "compactor: malformed request" (compactor_ffi_reads_only_requests)
# A1: Rust keeps the texts, relays the state the entry answered (tries left, calls made, the best reply's length) and cuts the text an end names to node bytes (rules/compactor.rs; trusted, not proven here).

import Base
import ../bend/compactor.bend as C
import ../bend/ffi_compactor.bend as FC
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../bend/optchat/info.bend as OInfo
import ../bend/optchat/node.bend as ONode
import ../bend/optchat/queue.bend as OQueue
import ../bend/optchat/state.bend as OState

# Terms
# -----

# a text's length in UTF-8 bytes: each character's width (RFC 3629: a
# character is 1 to 4 bytes)
def bytes(t: List<&2, C.W>) -> Nat:
  match t:
    case Nil{}:
      0n
    case c <> rest:
      match c:
        case C.W1{}:
          1n+bytes(rest)
        case C.W2{}:
          2n+bytes(rest)
        case C.W3{}:
          3n+bytes(rest)
        case C.W4{}:
          4n+bytes(rest)

# a reply of n bytes is shorter than the best reply so far (any reply is,
# before the first)
def below(best: Maybe<&2, List<&2, C.W>>, n: Nat) -> Bool:
  match best:
    case None{}:
      True{}
    case Some{a}:
      Nat.is_lt(n, bytes(a))

# the replies ps are ones a line asks again after, from the best reply
# best: each a text past the node and shorter than the one before it
def asks(ps: List<&2, C.Reply>, +node: Nat, best: Maybe<&2, List<&2, C.W>>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case r <> rest:
      match r:
        case C.Erred{}:
          False{}
        case C.Says{+ws}:
          Bool.and(Bool.and(Nat.is_lt(node, bytes(ws)), below(best, bytes(ws))), asks(rest, node, Some{ws}))

# the last text among ps, else best
def last_said(ps: List<&2, C.Reply>, best: Maybe<&2, List<&2, C.W>>) -> Maybe<&2, List<&2, C.W>>:
  match ps:
    case Nil{}:
      best
    case r <> rest:
      match r:
        case C.Erred{}:
          last_said(rest, best)
        case C.Says{ws}:
          last_said(rest, Some{ws})

# the best reply, else the input
def or_input(best: Maybe<&2, List<&2, C.W>>, input: List<&2, C.W>) -> List<&2, C.W>:
  match best:
    case None{}:
      input
    case Some{b}:
      b

# no reply comes next, or a provider error
def fails_next(rs: List<&2, C.Reply>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      match r:
        case C.Erred{}:
          True{}
        case C.Says{ws}:
          False{}

# a reply of n bytes is not shorter than the best reply (there is one)
def not_shorter(best: Maybe<&2, List<&2, C.W>>, n: Nat) -> Bool:
  match best:
    case None{}:
      False{}
    case Some{a}:
      Nat.is_le(bytes(a), n)

# a failed call, or a line of 1 to node bytes
def within(+node: Nat, m: Maybe<&2, List<&2, C.W>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{t}:
      +n = bytes(t)
      Bool.and(Nat.is_lt(0n, n), Nat.is_le(n, node))

def first_fit.pick(ok: Bool, t: List<&2, C.W>, rec: Maybe<&2, List<&2, C.W>>) -> Maybe<&2, List<&2, C.W>>:
  match ok:
    case True{}:
      Some{t}
    case False{}:
      rec

# the first reply of rs that fits: a text of 1 to node bytes (errors and
# empty replies are no fit)
def first_fit(+node: Nat, rs: List<&2, C.Reply>) -> Maybe<&2, List<&2, C.W>>:
  match rs:
    case Nil{}:
      None{}
    case r <> rest:
      match r:
        case C.Erred{}:
          first_fit(node, rest)
        case C.Says{t}:
          +ws = t
          first_fit.pick(Bool.and(Nat.is_lt(0n, bytes(ws)), Nat.is_le(bytes(ws), node)), ws, first_fit(node, rest))

# no fit was read, or the line is that fit
def FirstIs(want: Maybe<&2, List<&2, C.W>>, got: Maybe<&2, List<&2, C.W>>) -> Type:
  match want:
    case None{}:
      Unit
    case Some{f}:
      {got == Some{f} : Maybe<&2, List<&2, C.W>>}

# the text a reply says (none for an error)
def said_text(r: C.Reply) -> Maybe<&2, List<&2, C.W>>:
  match r:
    case C.Erred{}:
      None{}
    case C.Says{ws}:
      Some{ws}

# an end names the text Rust cuts: the reply just read (whole or cut),
# the best reply so far, or the input
def Names(e: C.Fin, said: Maybe<&2, List<&2, C.W>>, best: Maybe<&2, List<&2, C.W>>, input: List<&2, C.W>) -> Type:
  match e:
    case C.Whole{t}:
      {said == Some{t} : Maybe<&2, List<&2, C.W>>}
    case C.CutReply{t}:
      {said == Some{t} : Maybe<&2, List<&2, C.W>>}
    case C.CutBest{t}:
      {best == Some{t} : Maybe<&2, List<&2, C.W>>}
    case C.CutInput{t}:
      {input == t : List<&2, C.W>}
    case C.Errored{}:
      Unit

def NextNames(x: C.Next, said: Maybe<&2, List<&2, C.W>>, best: Maybe<&2, List<&2, C.W>>, input: List<&2, C.W>) -> Type:
  match x:
    case C.Ends{c, e}:
      Names(e, said, best, input)
    case C.Asks{st}:
      Unit

# the bytes of a reply's text (0 for an error)
def reply_bytes(r: C.Reply) -> Nat:
  match r:
    case C.Erred{}:
      0n
    case C.Says{ws}:
      bytes(ws)

# how many of the outcomes are failed calls
def failures(os: List<&2, C.Outcome>) -> Nat:
  match os:
    case Nil{}:
      0n
    case o <> rest:
      match o:
        case C.Failed{}:
          1n+failures(rest)
        case C.Built{}:
          failures(rest)
        case C.Disk{}:
          failures(rest)
        case C.Stopped{}:
          failures(rest)

# a line was saved among the outcomes
def saved(os: List<&2, C.Outcome>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case o <> rest:
      match o:
        case C.Built{}:
          True{}
        case C.Failed{}:
          saved(rest)
        case C.Disk{}:
          saved(rest)
        case C.Stopped{}:
          saved(rest)

def owed_after(built: Bool, n: Nat, f: Nat) -> C.Pend:
  match built:
    case True{}:
      C.Made{}
    case False{}:
      C.Owed{Nat.sub(n, f)}

# a line after the outcomes of its calls, from the counts alone: a built
# line stays built; an owed one with n failures left is built once a line
# was saved or more than n calls failed, else owed with n less the failed
# calls left
def after_all(os: List<&2, C.Outcome>, p: C.Pend) -> C.Pend:
  match p:
    case C.Made{}:
      C.Made{}
    case C.Owed{+n}:
      +os2 = os
      owed_after(Bool.or(saved(os2), Nat.is_lt(n, failures(os2))), n, failures(os2))

def keep_if(b: Bool, o: C.Outcome, rest: List<&2, C.Outcome>) -> List<&2, C.Outcome>:
  match b:
    case True{}:
      o <> rest
    case False{}:
      rest

# the outcomes of the calls of view line k, in the order they ended
def outcomes_of(es: List<&2, C.End>, +k: Nat) -> List<&2, C.Outcome>:
  match es:
    case Nil{}:
      Nil{}
    case C.End{j, o} <> rest:
      keep_if(Nat.is_eq(j, k), o, outcomes_of(rest, k))

# a view line after the outcomes os, when there is one
def line_after(os: List<&2, C.Outcome>, m: Maybe<&2, C.Pend>) -> Maybe<&2, C.Pend>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{after_all(os, p)}

# 1 when an outcome counts: its line m is pending, and the call saved the
# line or failed; else 0
def counts(m: Maybe<&2, C.Pend>, o: C.Outcome) -> Nat:
  match m:
    case None{}:
      0n
    case Some{p}:
      match p:
        case C.Made{}:
          0n
        case C.Owed{n}:
          match o:
            case C.Built{}:
              1n
            case C.Failed{}:
              1n
            case C.Disk{}:
              0n
            case C.Stopped{}:
              0n

# (H1) A compactor call always ends with a line that fits
# -------------------------------------------------------

# LAW line_calls_at_most_tries (R1): a line makes at most `tries` model calls
law line_calls_at_most_tries:
  for +tries: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for rs: List<&2, C.Reply>
  {Nat.is_le(C.Line.calls(C.line(tries, node, input, rs)), tries) == True{} : Bool}

# LAW line_error_fails (R2): after any replies ps the line asked again on
# (each a text past the node, each shorter than the one before), with a
# try left, a provider error or no reply at all fails the call, after one
# call more than ps
# EXCLUDES: an error read as an empty reply or skipped, an error after a
#   too long reply that ends with the best reply instead of failing, a
#   missing reply read as a success
law line_error_fails:
  for +t: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +ps: List<&2, C.Reply>
  for +rest: List<&2, C.Reply>
  for go: {asks(ps, node, None{}) == True{} : Bool}
  for none: {fails_next(rest) == True{} : Bool}
  {C.line(Nat.add(List.length(&2, C.Reply, ps), 1n+t), node, input, List.append(&2, C.Reply, ps, rest)) == C.Line{1n+List.length(&2, C.Reply, ps), None{}} : C.Line}

# LAW line_empty_is_a_try (R3): after any replies ps the line asked again
# on, with a try left, an empty (or thinking-only) reply is a try, not a
# failure: it ends the call, one call after ps, with the last of ps (the
# best reply) cut to node bytes, else the input cut
# EXCLUDES: an empty reply that fails the call or asks again, an empty
#   line, the input taken over a best reply, a call not counted
law line_empty_is_a_try:
  for +t: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +ps: List<&2, C.Reply>
  for +rest: List<&2, C.Reply>
  for go: {asks(ps, node, None{}) == True{} : Bool}
  {C.line(Nat.add(List.length(&2, C.Reply, ps), 1n+t), node, input, List.append(&2, C.Reply, ps, C.Says{Nil{}} <> rest)) == C.Line{1n+List.length(&2, C.Reply, ps), Some{C.cut(or_input(last_said(ps, None{}), input), node)}} : C.Line}

# LAW line_takes_fit (R4): after any replies ps the line asked again on,
# with a try left, a reply of 1 to node bytes is the line, whole, one
# call after ps
# EXCLUDES: a fitting reply cut, skipped or asked about again, a line
#   that stops before it reads the reply, a call not counted
law line_takes_fit:
  for +t: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +ps: List<&2, C.Reply>
  for +f: List<&2, C.W>
  for +rest: List<&2, C.Reply>
  for go: {asks(ps, node, None{}) == True{} : Bool}
  for fit: {Bool.and(Nat.is_lt(0n, bytes(f)), Nat.is_le(bytes(f), node)) == True{} : Bool}
  {C.line(Nat.add(List.length(&2, C.Reply, ps), 1n+t), node, input, List.append(&2, C.Reply, ps, C.Says{f} <> rest)) == C.Line{1n+List.length(&2, C.Reply, ps), Some{f}} : C.Line}

# LAW line_takes_first_fit (R4): when a reply the line read fits (1 to
# node bytes), the line is the first such reply
law line_takes_first_fit:
  for +tries: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +rs: List<&2, C.Reply>
  FirstIs(first_fit(node, List.take(&2, C.Reply, rs, C.Line.calls(C.line(tries, node, input, rs)))), C.Line.line(C.line(tries, node, input, rs)))

# LAW line_stops_when_not_shorter (R5): after replies ps the line asked
# again on, at least one, with a try left, a reply b not shorter than the
# last of them (the best reply) ends the call, one call after ps, with the
# best reply cut to node bytes
# EXCLUDES: a line that keeps asking while the replies do not get
#   shorter, one that ends with the longer reply or the input, a call not
#   counted
law line_stops_when_not_shorter:
  for +t: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +ps: List<&2, C.Reply>
  for +b: List<&2, C.W>
  for +rest: List<&2, C.Reply>
  for go: {asks(ps, node, None{}) == True{} : Bool}
  for longer: {not_shorter(last_said(ps, None{}), bytes(b)) == True{} : Bool}
  {C.line(Nat.add(List.length(&2, C.Reply, ps), 1n+t), node, input, List.append(&2, C.Reply, ps, C.Says{b} <> rest)) == C.Line{1n+List.length(&2, C.Reply, ps), Some{C.cut(or_input(last_said(ps, None{}), input), node)}} : C.Line}

# LAW line_out_of_tries (R6): a line whose tries all went to replies it
# asked again on (no try at all: none) ends after those calls with the
# last of them (the shortest) cut to node bytes, else the input cut
# EXCLUDES: a call past the tries, a line that fails or keeps the input
#   when it has a best reply, the first reply taken over the shortest
law line_out_of_tries:
  for +node: Nat
  for +input: List<&2, C.W>
  for +ps: List<&2, C.Reply>
  for +rest: List<&2, C.Reply>
  for go: {asks(ps, node, None{}) == True{} : Bool}
  {C.line(List.length(&2, C.Reply, ps), node, input, List.append(&2, C.Reply, ps, rest)) == C.Line{List.length(&2, C.Reply, ps), Some{C.cut(or_input(last_said(ps, None{}), input), node)}} : C.Line}

# LAW cut_is_a_start_within (R7): a cut of a text is a start of it (some
# rest follows it) of at most room bytes
# EXCLUDES: a cut that drops or changes a character inside the text, one
#   past the room
law cut_is_a_start_within:
  for +t: List<&2, C.W>
  for +room: Nat
  exs rest: List<&2, C.W>
  {(List.append(&2, C.W, C.cut(t, room), rest), Nat.is_le(bytes(C.cut(t, room)), room)) == (t, True{}) : List<&2, C.W> & Bool}

# LAW cut_longest (R7): every start p of a text within room bytes is at
# most as long (in characters) as the cut: the cut is the longest start
# that fits
# EXCLUDES: a cut that stops early (an empty cut, one a character short)
law cut_longest:
  for +p: List<&2, C.W>
  for +q: List<&2, C.W>
  for +room: Nat
  for fit: {Nat.is_le(bytes(p), room) == True{} : Bool}
  {Nat.is_le(List.length(&2, C.W, p), List.length(&2, C.W, C.cut(List.append(&2, C.W, p, q), room))) == True{} : Bool}

# LAW line_fits (R8): with an input that is not empty and a node of at
# least 4 bytes (a character's widest), the line has 1 to node bytes, or
# the call failed
law line_fits:
  for +tries: Nat
  for +k: Nat
  for +c: C.W
  for +rest: List<&2, C.W>
  for +rs: List<&2, C.Reply>
  {within(4n+k, C.Line.line(C.line(tries, 4n+k, c <> rest, rs))) == True{} : Bool}

# (H2) A turn never waits forever for the memory
# ----------------------------------------------
# The settle of bend/compactor.bend, the need-first queue of
# bend/optchat/queue.bend (H2.1).

# LAW pend_run_counts (R10): a line after the outcomes of its calls, in
# order, is what the counts say: a built line stays built; a line owed
# with n failures left is built once a line was saved or more than n
# calls failed, else it is owed with n less the failed calls left (a
# disk error and a stop count for nothing)
# EXCLUDES: a cap reached early (a failure with failures left that
#   builds) or late, a failure that counts down by two or not at all, a
#   disk error or a stop that counts, a save that does not build, a built
#   line owed again
law pend_run_counts:
  for +os: List<&2, C.Outcome>
  for +p: C.Pend
  {C.Pend.run(os, p) == after_all(os, p) : C.Pend}

# LAW fail_cap_builds (R10): a line with n failures left is built once n+1 of its calls failed,
# whatever came between them (disk errors, stops, a saved line)
law fail_cap_builds:
  for n: Nat
  for os: List<&2, C.Outcome>
  for many: {Nat.is_le(1n+n, failures(os)) == True{} : Bool}
  {C.Pend.run(os, C.Owed{n}) == C.Made{} : C.Pend}

# LAW settle_run_lines (R11): after the outcomes of any calls, in the
# order they ended, view line k is line k after the outcomes of its own
# calls (pend_run_counts), and there is a line k after exactly when there
# was one before
# EXCLUDES: an outcome applied to another line, dropped, repeated or
#   reordered, a line added or dropped, a run that keeps the lines as
#   they were
law settle_run_lines:
  for +es: List<&2, C.End>
  for +ps: List<&2, C.Pend>
  for +k: Nat
  {List.get(&2, C.Pend, C.run(es, ps), k) == line_after(outcomes_of(es, k), List.get(&2, C.Pend, ps, k)) : Maybe<&2, C.Pend>}

# LAW settle_hits_one (R12): one outcome counts 1 when its line is pending
# and its call saved the line or failed, else 0 (a disk error, a stop, a
# built line, a call of no view line)
# EXCLUDES: hits that count nothing, or a disk error, a stop, a built line
law settle_hits_one:
  for +ps: List<&2, C.Pend>
  for +k: Nat
  for +o: C.Outcome
  {C.hits([C.End{k, o}], ps) == counts(List.get(&2, C.Pend, ps, k), o) : Nat}

# LAW settle_hits_split (R12): the outcomes of a then b count those of a
# plus those of b on the lines a left
# EXCLUDES: hits that read the lines from before earlier outcomes, or skip
#   or repeat an outcome
law settle_hits_split:
  for +a: List<&2, C.End>
  for +b: List<&2, C.End>
  for +ps: List<&2, C.Pend>
  {C.hits(List.append(&2, C.End, a, b), ps) == Nat.add(C.hits(a, ps), C.hits(b, C.run(a, ps))) : Nat}

# LAW settle_falls (R13): each outcome that counts (a saved line, a failed call) of a
# pending line's call lowers the measure
law settle_falls:
  for +ps: List<&2, C.Pend>
  for +k: Nat
  for +o: C.Outcome
  for due: {C.pending_at(ps, k) == True{} : Bool}
  for lands: {C.Outcome.lands(o) == True{} : Bool}
  {Nat.is_lt(C.measure(C.hit(ps, k, o)), C.measure(ps)) == True{} : Bool}

# LAW settle_bounded (R13): after any outcomes, disk errors and stops among them, those that
# counted for a pending line plus the measure left are at most the
# measure at the start
law settle_bounded:
  for +es: List<&2, C.End>
  for +ps: List<&2, C.Pend>
  {Nat.is_le(Nat.add(C.hits(es, ps), C.measure(C.run(es, ps))), C.measure(ps)) == True{} : Bool}

# LAW settle_reached (R13): so once as many outcomes as the measure counted for pending lines,
# every line of the view is built
law settle_reached:
  for +es: List<&2, C.End>
  for +ps: List<&2, C.Pend>
  for enough: {Nat.is_le(C.measure(ps), C.hits(es, ps)) == True{} : Bool}
  {C.settled(C.run(es, ps)) == True{} : Bool}

# LAW settle_start (R13): when a turn starts to wait, the measure is the failure cap (1+p)
# times the view's unbuilt lines
law settle_start:
  for +p: Nat
  for +info: OInfo.Info
  for +v: List<&2, ONode.Node>
  {C.measure(C.settle.start(p, info, v)) == Nat.mul(C.unbuilt(info, v), 1n+p) : Nat}

# LAW need_first (R14): while a turn waits, every node the queue starts is a line of the
# view that is not built
law need_first:
  for +cfg: OState.Cfg
  for +s: OState.St
  {C.needed(OState.St.info(s), OState.St.view(s), OQueue.cands.need(cfg, s)) == True{} : Bool}

# LAW need_first_due (R14): under the due mark too (OQueue.cands.need.due):
# every node a waiting turn's queue starts is a line of the whole view
# that is not built
# EXCLUDES: a merge or a non-view node started while a turn waits
law need_first_due:
  for +cfg: OState.Cfg
  for +s: OState.St
  for +due: Nat
  {C.needed(OState.St.info(s), OState.St.view(s), OQueue.cands.need.due(cfg, s, due)) == True{} : Bool}

# LAW need_first_running (R14): when a turn starts to wait, every call it does not need stops
# (OQueue.St.wait): then every running call and every call the queue starts
# is for a line of the view that is not built
law need_first_running:
  for +cfg: OState.Cfg
  for +s: OState.St
  {C.needed(OState.St.info(s), OState.St.view(s), List.append(&2, ONode.Node, OState.St.busy(OQueue.St.wait(s)), OQueue.cands.need(cfg, OQueue.St.wait(s)))) == True{} : Bool}

# LAW wait_keeps_needed (R14): and the wait (OQueue.St.wait) stops no call
# the view needs: every running call of a view line not built still runs
# after it
law wait_keeps_needed:
  for +s: OState.St
  {C.kept(OState.St.info(s), OState.St.view(s), OState.St.busy(s), OState.St.busy(OQueue.St.wait(s))) == True{} : Bool}

# The line, one reply at a time (R9)
# ----------------------------------

# LAW line_steps (R9): the steps the shipped compactor takes, driven over the model's replies from a line's open, are `line` itself: every law of `line` holds for them
law line_steps:
  for +tries: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +rs: List<&2, C.Reply>
  {C.line.drive(rs, C.line.open(tries, node, input), node) == C.line(tries, node, input, rs) : C.Line}

# LAW open_end_names_its_text (R9): a line that ends as it opens (no
# tries) ends with the input: it has no reply and no best reply yet
# EXCLUDES: an open that tells Rust to keep a reply (whole or cut) or a
#   best reply it does not have
law open_end_names_its_text:
  for +t: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  NextNames(C.line.open(t, node, input), None{}, None{}, input)

# LAW step_end_names_its_text (R9): an end after a reply names the text
# Rust cuts by its tag: the reply just read for a whole or cut reply, the
# line's best reply for the best cut, the line's input for the input cut
# EXCLUDES: a tag that names another text than the one the model's line
#   holds (the best reply under the reply's tag, the input under the best
#   reply's)
law step_end_names_its_text:
  for +left: Nat
  for +made: Nat
  for +node: Nat
  for +best: Maybe<&2, List<&2, C.W>>
  for +bl: Nat
  for +input: List<&2, C.W>
  for +r: C.Reply
  NextNames(C.line.step(C.Lst{left, made, node, best, bl, input}, r), said_text(r), best, input)

# The entry (bend/ffi_compactor.bend)
# -----------------------------------
# Rust keeps the texts and sends their lengths in UTF-8 bytes; the model
# decides each step of a line (line.open, line.step) and the failure cap
# (Pend.after). The spellers below write what Rust writes, with the wire
# primitives only.

# a line's shortest reply so far: 0 none | 1 and its length
def spell_best(b: Maybe<&2, List<&2, C.W>>, bl: Nat, rest: String) -> String:
  match b:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{t}:
      Wr.put_nat(1n, Wr.put_nat(bl, rest))

# a reply: 0 a provider error | 1 and its text's length
def spell_reply(r: C.Reply) -> String:
  match r:
    case C.Erred{}:
      Wr.put_nat(0n, "")
    case C.Says{ws}:
      Wr.put_nat(1n, Wr.put_nat(bytes(ws), ""))

# a line opens with t tries
def spell_open(t: Nat) -> String:
  Wr.put_nat(0n, Wr.put_nat(t, ""))

# a reply r to the line st: tries left, calls made, node, best, reply
def spell_step(st: C.Lst, r: C.Reply) -> String:
  match st:
    case C.Lst{l, m, n, b, bl, i}:
      Wr.put_nat(1n, Wr.put_nat(l, Wr.put_nat(m, Wr.put_nat(n, spell_best(b, bl, spell_reply(r))))))

def spell_pend(p: C.Pend, rest: String) -> String:
  match p:
    case C.Made{}:
      Wr.put_nat(0n, rest)
    case C.Owed{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

def spell_outcome(o: C.Outcome) -> String:
  match o:
    case C.Built{}:
      Wr.put_nat(0n, "")
    case C.Failed{}:
      Wr.put_nat(1n, "")
    case C.Disk{}:
      Wr.put_nat(2n, "")
    case C.Stopped{}:
      Wr.put_nat(3n, "")

# a call of the pending line p ended with o
def spell_after(p: C.Pend, o: C.Outcome) -> String:
  Wr.put_nat(2n, spell_pend(p, spell_outcome(o)))

# how a line ends: 0 the reply whole, 1 the reply cut, 2 the best reply
# cut, 3 the input cut, 4 the call failed
def spell_fin(e: C.Fin) -> String:
  match e:
    case C.Whole{t}:
      Wr.put_nat(0n, "")
    case C.CutReply{t}:
      Wr.put_nat(1n, "")
    case C.CutBest{t}:
      Wr.put_nat(2n, "")
    case C.CutInput{t}:
      Wr.put_nat(3n, "")
    case C.Errored{}:
      Wr.put_nat(4n, "")

# the reply Rust reads: 0 the line ends after c calls, then how | 1 the
# next call goes, then the tries left, the calls made and the best
# reply's length (Maybe)
def spell_next(x: C.Next) -> String:
  match x:
    case C.Ends{c, e}:
      Wr.put_nat(0n, Wr.put_nat(c, spell_fin(e)))
    case C.Asks{st}:
      match st:
        case C.Lst{l, m, n, b, bl, i}:
          Wr.put_nat(1n, Wr.put_nat(l, Wr.put_nat(m, spell_best(b, bl, ""))))

# every number Rust writes fits the wire
def best_fits(b: Maybe<&2, List<&2, C.W>>, bl: Nat) -> Bool:
  match b:
    case None{}:
      True{}
    case Some{t}:
      LawsBase.wire_fits(bl)

def reply_fits(r: C.Reply) -> Bool:
  match r:
    case C.Erred{}:
      True{}
    case C.Says{ws}:
      LawsBase.wire_fits(bytes(ws))

def step_fits(st: C.Lst, r: C.Reply) -> Bool:
  match st:
    case C.Lst{l, m, n, b, bl, i}:
      Bool.and(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(n), Bool.and(best_fits(b, bl), reply_fits(r)))))

def pend_fits(p: C.Pend) -> Bool:
  match p:
    case C.Made{}:
      True{}
    case C.Owed{n}:
      LawsBase.wire_fits(n)

# a request Rust spells: a line opens with t tries; a reply r to the line
# st; a call of the pending line p ended with o
type Ask is Data:
  AOpen{t: Nat}
  AStep{st: C.Lst, r: C.Reply}
  AAfter{p: C.Pend, o: C.Outcome}

def spell_ask(a: Ask) -> String:
  match a:
    case AOpen{t}:
      spell_open(t)
    case AStep{st, r}:
      spell_step(st, r)
    case AAfter{p, o}:
      spell_after(p, o)

def ask_fits(a: Ask) -> Bool:
  match a:
    case AOpen{t}:
      LawsBase.wire_fits(t)
    case AStep{st, r}:
      step_fits(st, r)
    case AAfter{p, o}:
      pend_fits(p)

# LAW compactor_ffi_open (R15): a line that opens answers the model's line.open, for every node and input (Rust keeps them)
law compactor_ffi_open:
  for +t: Nat
  for node: Nat
  for input: List<&2, C.W>
  for fits: {LawsBase.wire_fits(t) == True{} : Bool}
  {FC.ffi(spell_open(t)) == spell_next(C.line.open(t, node, input)) : String}

# LAW compactor_ffi_step (R15): on every line state and reply whose numbers fit the wire (tries left, calls made, node, best reply's length, reply's length: at most 14 digits), the entry answers the model's line.step, read from the lengths Rust sends: the same end after the same calls, or the next call with the same tries left, calls made and best reply's length
law compactor_ffi_step:
  for +st: C.Lst
  for +r: C.Reply
  for fits: {step_fits(st, r) == True{} : Bool}
  {FC.ffi(spell_step(st, r)) == spell_next(C.line.step(st, r)) : String}

# LAW line_step_node_beyond_reply (R15): two node sizes, both at least the
# reply's length, get the same answer on the wire: so Rust's saturation
# of a node past the wire bound (no reply that long fits in memory)
# changes no decision
# EXCLUDES: a decision that reads the node's size beyond whether the reply
#   fits it
law line_step_node_beyond_reply:
  for +left: Nat
  for +made: Nat
  for +n1: Nat
  for +n2: Nat
  for +best: Maybe<&2, List<&2, C.W>>
  for +bl: Nat
  for +input: List<&2, C.W>
  for +r: C.Reply
  for le1: {Nat.is_le(reply_bytes(r), n1) == True{} : Bool}
  for le2: {Nat.is_le(reply_bytes(r), n2) == True{} : Bool}
  {spell_next(C.line.step(C.Lst{left, made, n1, best, bl, input}, r)) == spell_next(C.line.step(C.Lst{left, made, n2, best, bl, input}, r)) : String}

# LAW compactor_ffi_after (R15): a call of a pending line that ended answers the model's Pend.after
law compactor_ffi_after:
  for +p: C.Pend
  for +o: C.Outcome
  for fits: {pend_fits(p) == True{} : Bool}
  {FC.ffi(spell_after(p, o)) == spell_pend(C.Pend.after(p, o), "") : String}

# LAW compactor_ffi_reads_only_requests (R16): every answer but exactly the
# error form "compactor: malformed request" answers a request: the input
# is exactly the spelling of a request whose numbers fit the wire (whose
# answer compactor_ffi_open, compactor_ffi_step or compactor_ffi_after
# pins)
# EXCLUDES: a decoder that accepts an unknown request, Maybe, reply or
#   outcome tag, a missing field or input left over, and answers it
#   anyway (a default instead of the error form), or refuses with another
#   text
law compactor_ffi_reads_only_requests:
  for +s: String
  for other: {String.eq(FC.ffi(s), Wr.err("compactor: malformed request")) == False{} : Bool}
  exs a: Ask
  {(s, ask_fits(a)) == (spell_ask(a), True{}) : String & Bool}

# LAW compactor_ffi_example: anchor: the bytes Rust sends and reads: a line of 5 tries opens; a 700-byte first reply asks again; a 600-byte follow-up on the last try ends cut; a follow-up not shorter ends with the best cut; an empty reply ends with the input cut; an error fails; a reply at the node's size is whole; the last failure left builds a node, a failure with two left leaves one, a disk error keeps it owed; an unknown tag and input left over are refused
law compactor_ffi_example:
  {FC.ffi("0,5,") == "1,5,0,0," : String} &
  {FC.ffi("1,5,0,512,0,1,700,") == "1,4,1,1,700," : String} &
  {FC.ffi("1,1,4,512,1,700,1,600,") == "0,5,1," : String} &
  {FC.ffi("1,4,1,512,1,700,1,700,") == "0,2,2," : String} &
  {FC.ffi("1,5,0,512,0,1,0,") == "0,1,3," : String} &
  {FC.ffi("1,5,0,512,0,0,") == "0,1,4," : String} &
  {FC.ffi("1,4,1,512,1,700,1,512,") == "0,2,0," : String} &
  {FC.ffi("2,1,0,1,") == "0," : String} &
  {FC.ffi("2,1,2,1,") == "1,1," : String} &
  {FC.ffi("2,1,2,2,") == "1,2," : String} &
  {FC.ffi("3,") == SCon{'E', SCon{' ', "compactor: malformed request"}} : String} &
  {FC.ffi("0,5,x") == SCon{'E', SCon{' ', "compactor: malformed request"}} : String}

def open_spec(t: Nat, n: Nat, i: List<&2, C.W>) -> C.Next:
  match t:
    case 0n:
      C.Ends{0n, C.CutInput{i}}
    case 1n+q:
      C.Asks{C.Lst{1n+q, 0n, n, None{}, 0n, i}}

# LAW line_open_exact: a line opens with exactly its tries, no call made and no best reply, or with no tries ends at once with the input cut
law line_open_exact:
  for t: Nat
  for n: Nat
  for i: List<&2, C.W>
  {C.line.open(t, n, i) == open_spec(t, n, i) : C.Next}

# The model's own terms, independently: a line opens with its tries, or
# ends at once with the input cut; a reply with tries left ends the line
# when it is an error (failed), empty (the best, else the input, cut),
# within the node (whole), not shorter than the best (the best cut) or the
# last try (cut), and else asks again with one try less and it as the
# best; with no try left the line ends with the best, else the input, cut
def end_spec(b: Maybe<&2, List<&2, C.W>>, i: List<&2, C.W>) -> C.Fin:
  match b:
    case None{}:
      C.CutInput{i}
    case Some{t}:
      C.CutBest{t}

# the reply is shorter than the best (always, before the first)
def shorter_spec(b: Maybe<&2, List<&2, C.W>>, bl: Nat, len: Nat) -> Bool:
  match b:
    case None{}:
      True{}
    case Some{t}:
      Nat.is_lt(len, bl)

def step_spec.long(shorter: Bool, q: Nat, m: Nat, n: Nat, b: Maybe<&2, List<&2, C.W>>, i: List<&2, C.W>, ws: List<&2, C.W>, len: Nat) -> C.Next:
  match shorter:
    case False{}:
      C.Ends{1n+m, end_spec(b, i)}
    case True{}:
      match q:
        case 0n:
          C.Ends{1n+m, C.CutReply{ws}}
        case 1n+k:
          C.Asks{C.Lst{1n+k, 1n+m, n, Some{ws}, len, i}}

def step_spec.text(fits: Bool, shorter: Bool, q: Nat, m: Nat, n: Nat, b: Maybe<&2, List<&2, C.W>>, i: List<&2, C.W>, ws: List<&2, C.W>, len: Nat) -> C.Next:
  match fits:
    case True{}:
      C.Ends{1n+m, C.Whole{ws}}
    case False{}:
      step_spec.long(shorter, q, m, n, b, i, ws, len)

def step_spec(st: C.Lst, r: C.Reply) -> C.Next:
  match st:
    case C.Lst{l, m, +n, +b, +bl, +i}:
      match l:
        case 0n:
          C.Ends{m, end_spec(b, i)}
        case 1n+q:
          match r:
            case C.Erred{}:
              C.Ends{1n+m, C.Errored{}}
            case C.Says{ws}:
              match ws:
                case Nil{}:
                  C.Ends{1n+m, end_spec(b, i)}
                case +c <> +t:
                  +len = bytes(c <> t)
                  step_spec.text(Nat.is_le(len, n), shorter_spec(b, bl, len), q, m, n, b, i, c <> t, len)

# LAW line_step_exact: one reply to a line is exactly: with no try left the best (else the input) cut; an error fails the call; an empty reply ends with the best (else the input) cut; a reply within the node's bytes is the line; one not shorter than the best ends with the best cut; the last try ends cut; else the next call goes with one try less, one more call and the reply (its length in bytes) as the best
law line_step_exact:
  for st: C.Lst
  for r: C.Reply
  {C.line.step(st, r) == step_spec(st, r) : C.Next}

# Reader: the requests the entry accepts, read with the wire primitives;
# a request as its numbers: 0 open | 1 a reply | 2 an ended call
type Ask_orig is Data:
  AOpen_orig{t: Nat}
  AStep_orig{l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, r: Maybe<&2, Nat>}
  AAfter_orig{p: C.Pend, o: Nat}

def read_after.how.tag(p: C.Pend, t: Nat, s: String) -> Wr.Dec<Ask_orig>:
  match t:
    case 0n:
      Wr.Got{AAfter_orig{p, 0n}, s}
    case 1n:
      Wr.Got{AAfter_orig{p, 1n}, s}
    case 2n:
      Wr.Got{AAfter_orig{p, 2n}, s}
    case 3n:
      Wr.Got{AAfter_orig{p, 3n}, s}
    case 4n+q:
      Wr.Bad{}

def read_after.how(p: C.Pend, r: Wr.Dec<Nat>) -> Wr.Dec<Ask_orig>:
  match r:
    case Wr.Got{t, s}:
      read_after.how.tag(p, t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_after.owed(r: Wr.Dec<Nat>) -> Wr.Dec<Ask_orig>:
  match r:
    case Wr.Got{n, s}:
      read_after.how(C.Owed{n}, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_after.tag(t: Nat, s: String) -> Wr.Dec<Ask_orig>:
  match t:
    case 0n:
      read_after.how(C.Made{}, Wr.get_nat(s))
    case 1n:
      read_after.owed(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def read_after(r: Wr.Dec<Nat>) -> Wr.Dec<Ask_orig>:
  match r:
    case Wr.Got{t, s}:
      read_after.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_open(r: Wr.Dec<Nat>) -> Wr.Dec<Ask_orig>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{AOpen_orig{t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_m.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Some{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_m.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      read_m.some(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

# a Maybe<Nat>: 0 none | 1 and the Nat (a reply: 0 an error | 1 and its length)
def read_m(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      read_m.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_step.reply(l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Ask_orig>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{AStep_orig{l, m, n, b, x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_step.best(l: Nat, m: Nat, n: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Ask_orig>:
  match r:
    case Wr.Got{b, s}:
      read_step.reply(l, m, n, b, read_m(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_step.node(l: Nat, m: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Ask_orig>:
  match r:
    case Wr.Got{n, s}:
      read_step.best(l, m, n, read_m(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_step.made(l: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Ask_orig>:
  match r:
    case Wr.Got{m, s}:
      read_step.node(l, m, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_step(r: Wr.Dec<Nat>) -> Wr.Dec<Ask_orig>:
  match r:
    case Wr.Got{l, s}:
      read_step.made(l, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tag(t: Nat, s: String) -> Wr.Dec<Ask_orig>:
  match t:
    case 0n:
      read_open(Wr.get_nat(s))
    case 1n:
      read_step(Wr.get_nat(s))
    case 2n:
      read_after(Wr.get_nat(s))
    case 3n+p:
      Wr.Bad{}

def read_ask.go(r: Wr.Dec<Nat>) -> Wr.Dec<Ask_orig>:
  match r:
    case Wr.Got{t, s}:
      read_ask.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: Ask_orig) -> Maybe<&2, Ask_orig>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(r: Wr.Dec<Ask_orig>) -> Maybe<&2, Ask_orig>:
  match r:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, Ask_orig>:
  read_ask.whole(read_ask.go(Wr.get_nat(s)))

# a pending line after one of its calls: a saved line builds it, a failed
# call with no failures left builds it (from its input) and with some
# left counts one down; a disk error and a stop change nothing; a built
# line stays built
def after_spec.failed(k: Nat) -> C.Pend:
  match k:
    case 0n:
      C.Made{}
    case 1n+j:
      C.Owed{j}

def after_spec(p: C.Pend, o: C.Outcome) -> C.Pend:
  match p:
    case C.Made{}:
      C.Made{}
    case C.Owed{k}:
      match o:
        case C.Built{}:
          C.Made{}
        case C.Failed{}:
          after_spec.failed(k)
        case C.Disk{}:
          C.Owed{k}
        case C.Stopped{}:
          C.Owed{k}

# a text of n bytes, one-byte characters
def ones(n: Nat) -> List<&2, C.W>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      C.W1{} <> ones(k)

# the shortest reply so far as read: 0 none | 1 a text of that length
def ask_best(b: Maybe<&2, Nat>) -> Maybe<&2, List<&2, C.W>>:
  match b:
    case None{}:
      None{}
    case Some{k}:
      Some{ones(k)}

def ask_bl(b: Maybe<&2, Nat>) -> Nat:
  match b:
    case None{}:
      0n
    case Some{k}:
      k

# how a call ended as read: 0 saved, 1 failed, 2 the disk, 3 stopped (the
# reader reads no other tag)
def ask_outcome(o: Nat) -> C.Outcome:
  match o:
    case 0n:
      C.Built{}
    case 1n:
      C.Failed{}
    case 2n:
      C.Disk{}
    case 3n+q:
      C.Stopped{}

# the reply as read: 0 a provider error | 1 a text of that length
def ask_reply(x: Maybe<&2, Nat>) -> C.Reply:
  match x:
    case None{}:
      C.Erred{}
    case Some{k}:
      C.Says{ones(k)}

# the answer to a request read: a line opens (open_spec), a reply to a
# line (step_spec, the line's input left out: Rust keeps it), a call of a
# pending line ended (after_spec)
def spec_answer(a: Ask_orig) -> String:
  match a:
    case AOpen_orig{t}:
      spell_next(open_spec(t, 0n, Nil{}))
    case AStep_orig{l, m, n, +b, x}:
      spell_next(step_spec(C.Lst{l, m, n, ask_best(b), ask_bl(b), Nil{}}, ask_reply(x)))
    case AAfter_orig{p, o}:
      spell_pend(after_spec(p, ask_outcome(o)), "")

# the answer to an input: no whole request, the error form
def spec_entry(m: Maybe<&2, Ask_orig>) -> String:
  match m:
    case None{}:
      SCon{'E', SCon{' ', "compactor: malformed request"}}
    case Some{a}:
      spec_answer(a)

# LAW compactor_ffi_spec: every input is answered from the spec alone: exactly one request (read_ask) gets the decision open_spec, step_spec or after_spec takes on the numbers it carries, every other input exactly the error form 'E ', then "compactor: malformed request"
# EXCLUDES: an input other than one whole request answered with a value (a
#   second spelling, input left over), a decision on a read request that
#   is not the spec's, a reply that depends on anything but the input
law compactor_ffi_spec:
  for +s: String
  {FC.ffi(s) == spec_entry(read_ask(s)) : String}

# LAW compactor_ffi_malformed_exact: every input that is not exactly one request gets exactly the error form 'E ', then "compactor: malformed request"
law compactor_ffi_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, Ask_orig>}
  {FC.ffi(s) == SCon{'E', SCon{' ', "compactor: malformed request"}} : String}

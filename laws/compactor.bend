# eukhe: the laws of area compactor

import Base
import ../bend/compactor.bend as C
import ../bend/ffi_compactor.bend as FC
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../bend/optchat/info.bend as OInfo
import ../bend/optchat/node.bend as ONode
import ../bend/optchat/queue.bend as OQueue
import ../bend/optchat/state.bend as OState

# (H1) A compactor call always ends with a line that fits
# -------------------------------------------------------
# LAWS.bend H1, the model in bend/compactor.bend. A reply is free:
# any text, empty, thinking only, an error, missing.

# LAW line_calls_at_most_tries: a line makes at most `tries` model calls
law line_calls_at_most_tries:
  for +tries: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for rs: List<&2, C.Reply>
  {Nat.is_le(C.Line.calls(C.line(tries, node, input, rs)), tries) == True{} : Bool}

# LAW line_fits: with an input that is not empty and a node of at least 4 bytes
# (a character's widest), the line has 1 to node bytes, or the call failed
law line_fits:
  for +tries: Nat
  for +k: Nat
  for +c: C.W
  for +rest: List<&2, C.W>
  for +rs: List<&2, C.Reply>
  {C.line.fits(4n+k, C.Line.line(C.line(tries, 4n+k, c <> rest, rs))) == True{} : Bool}

# LAW line_takes_first_fit: when a reply the line read fits, the line is the first such reply
law line_takes_first_fit:
  for +tries: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +rs: List<&2, C.Reply>
  {C.line.first(C.first_fit(node, C.read(C.Line.calls(C.line(tries, node, input, rs)), rs)), C.Line.line(C.line(tries, node, input, rs))) == True{} : Bool}

# LAW line_stops_when_not_shorter: a follow-up not shorter than the best reply ends the line: the
# best reply, cut to node bytes, after 2 calls
law line_stops_when_not_shorter:
  for +t: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +a: List<&2, C.W>
  for +b: List<&2, C.W>
  for +rest: List<&2, C.Reply>
  for +over: {Nat.is_lt(node, C.Text.len(a)) == True{} : Bool}
  for +longer: {Nat.is_le(C.Text.len(a), C.Text.len(b)) == True{} : Bool}
  {C.line(2n+t, node, input, C.Says{a} <> C.Says{b} <> rest) == C.Line{2n, Some{C.cut(a, node)}} : C.Line}

# LAW line_empty_is_a_try: an empty (or thinking-only) reply is a try, not a failure: the
# line is the input cut to node bytes
law line_empty_is_a_try:
  for t: Nat
  for node: Nat
  for input: List<&2, C.W>
  for rest: List<&2, C.Reply>
  {C.line(1n+t, node, input, C.Says{Nil{}} <> rest) == C.Line{1n, Some{C.cut(input, node)}} : C.Line}

# LAW line_error_fails: a provider error fails the call
law line_error_fails:
  for t: Nat
  for node: Nat
  for input: List<&2, C.W>
  for rest: List<&2, C.Reply>
  {C.line(1n+t, node, input, C.Erred{} <> rest) == C.Line{1n, None{}} : C.Line}

# LAW fail_cap_builds: a line with n failures left is built once n+1 of its calls failed,
# whatever came between them (disk errors, stops, a saved line)
law fail_cap_builds:
  for n: Nat
  for os: List<&2, C.Outcome>
  for many: {Nat.is_le(1n+n, C.failures(os)) == True{} : Bool}
  {C.Pend.run(os, C.Owed{n}) == C.Made{} : C.Pend}

# (H2) A turn never waits forever for the memory
# ----------------------------------------------
# LAWS.bend H2: the need-first queue of bend/optchat/queue.bend, the settle
# of bend/compactor.bend.

# LAW need_first: while a turn waits, every node the queue starts is a line of the
# view that is not built
law need_first:
  for +cfg: OState.Cfg
  for +s: OState.St
  {C.needed(OState.St.info(s), OState.St.view(s), OQueue.cands.need(cfg, s)) == True{} : Bool}

# LAW need_first_running: when a turn starts to wait, every call it does not need stops
# (O.St.wait): then every running call and every call the queue starts
# is for a line of the view that is not built
law need_first_running:
  for +cfg: OState.Cfg
  for +s: OState.St
  {C.needed(OState.St.info(s), OState.St.view(s), List.append(&2, ONode.Node, OState.St.busy(OQueue.St.wait(s)), OQueue.cands.need(cfg, OQueue.St.wait(s)))) == True{} : Bool}

# LAW wait_keeps_needed: and it stops no call the view needs: a call of a view line not
# built still runs. Every waiting turn waits for the same view, so no
# turn's wait stops a call another waiting turn needs.
law wait_keeps_needed:
  for +s: OState.St
  {C.kept(OState.St.info(s), OState.St.view(s), OState.St.busy(s), OState.St.busy(OQueue.St.wait(s))) == True{} : Bool}

# LAW settle_falls: each outcome that counts (a saved line, a failed call) of a
# pending line's call lowers the measure
law settle_falls:
  for +ps: List<&2, C.Pend>
  for +k: Nat
  for +o: C.Outcome
  for due: {C.pending_at(ps, k) == True{} : Bool}
  for lands: {C.Outcome.lands(o) == True{} : Bool}
  {Nat.is_lt(C.measure(C.hit(ps, k, o)), C.measure(ps)) == True{} : Bool}

# LAW settle_bounded: after any outcomes, disk errors and stops among them, those that
# counted for a pending line plus the measure left are at most the
# measure at the start
law settle_bounded:
  for +es: List<&2, C.End>
  for +ps: List<&2, C.Pend>
  {Nat.is_le(Nat.add(C.hits(es, ps), C.measure(C.run(es, ps))), C.measure(ps)) == True{} : Bool}

# LAW settle_reached: so once as many outcomes as the measure counted for pending lines,
# every line of the view is built
law settle_reached:
  for +es: List<&2, C.End>
  for +ps: List<&2, C.Pend>
  for enough: {Nat.is_le(C.measure(ps), C.hits(es, ps)) == True{} : Bool}
  {C.settled(C.run(es, ps)) == True{} : Bool}

# LAW settle_start: when a turn starts to wait, the measure is the failure cap (1+p)
# times the view's unbuilt lines
law settle_start:
  for +p: Nat
  for +info: OInfo.Info
  for +v: List<&2, ONode.Node>
  {C.measure(C.settle.start(p, info, v)) == Nat.mul(C.unbuilt(info, v), 1n+p) : Nat}

# The entry (bend/ffi_compactor.bend)
# -----------------------------------
# Rust keeps the texts and sends their lengths in UTF-8 bytes; the model
# decides each step of a line (line.open, line.step) and the failure cap
# (Pend.after). The spellers below write what Rust writes, with the wire
# primitives only.

# a text's length in UTF-8 bytes: each character's width
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

def open_spec(t: Nat, n: Nat, i: List<&2, C.W>) -> C.Next:
  match t:
    case 0n:
      C.Ends{0n, C.CutInput{i}}
    case 1n+q:
      C.Asks{C.Lst{1n+q, 0n, n, None{}, 0n, i}}

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
              C.Ends{1n+m, C.Lost{}}
            case C.Says{ws}:
              match ws:
                case Nil{}:
                  C.Ends{1n+m, end_spec(b, i)}
                case +c <> +t:
                  +len = bytes(c <> t)
                  step_spec.text(Nat.is_le(len, n), shorter_spec(b, bl, len), q, m, n, b, i, c <> t, len)

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

# The helpers the H1 laws read, independently: a line fits when it has 1
# to node bytes; two texts are the same char by char; the first reply
# that fits; the replies a line of n calls read; the failed calls among
# outcomes; the cut (every character that fits in the room, in order)
def fits_spec(node: Nat, m: Maybe<&2, List<&2, C.W>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{t}:
      +n = bytes(t)
      Bool.and(Nat.is_lt(0n, n), Nat.is_le(n, node))

def w_tag(c: C.W) -> Nat:
  match c:
    case C.W1{}:
      1n
    case C.W2{}:
      2n
    case C.W3{}:
      3n
    case C.W4{}:
      4n

def same_spec(a: List<&2, C.W>, b: List<&2, C.W>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          True{}
        case y <> ys:
          False{}
    case x <> xs:
      match b:
        case Nil{}:
          False{}
        case y <> ys:
          Bool.and(Nat.is_eq(w_tag(x), w_tag(y)), same_spec(xs, ys))

def first_spec(want: Maybe<&2, List<&2, C.W>>, got: Maybe<&2, List<&2, C.W>>) -> Bool:
  match want:
    case None{}:
      True{}
    case Some{f}:
      match got:
        case None{}:
          False{}
        case Some{g}:
          same_spec(f, g)

def first_fit_spec.pick(ok: Bool, t: List<&2, C.W>, rec: Maybe<&2, List<&2, C.W>>) -> Maybe<&2, List<&2, C.W>>:
  match ok:
    case True{}:
      Some{t}
    case False{}:
      rec

def first_fit_spec(+node: Nat, rs: List<&2, C.Reply>) -> Maybe<&2, List<&2, C.W>>:
  match rs:
    case Nil{}:
      None{}
    case r <> rest:
      match r:
        case C.Erred{}:
          first_fit_spec(node, rest)
        case C.Says{t}:
          +ws = t
          first_fit_spec.pick(Bool.and(Nat.is_lt(0n, bytes(ws)), Nat.is_le(bytes(ws), node)), ws, first_fit_spec(node, rest))

def read_spec(n: Nat, rs: List<&2, C.Reply>) -> List<&2, C.Reply>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match rs:
        case Nil{}:
          Nil{}
        case r <> rest:
          r <> read_spec(p, rest)

def failures_spec(os: List<&2, C.Outcome>) -> Nat:
  match os:
    case Nil{}:
      0n
    case o <> rest:
      match o:
        case C.Failed{}:
          1n+failures_spec(rest)
        case C.Built{}:
          failures_spec(rest)
        case C.Disk{}:
          failures_spec(rest)
        case C.Stopped{}:
          failures_spec(rest)

# LAW line_fits_exact: the fit the H1 laws read is exactly: a failed call, or a line of 1 to node bytes
law line_fits_exact:
  for node: Nat
  for m: Maybe<&2, List<&2, C.W>>
  {C.line.fits(node, m) == fits_spec(node, m) : Bool}

# LAW line_first_exact: the first-fit check the H1 laws read is exactly: no reply fits, or the line is that reply char by char
law line_first_exact:
  for want: Maybe<&2, List<&2, C.W>>
  for got: Maybe<&2, List<&2, C.W>>
  {C.line.first(want, got) == first_spec(want, got) : Bool}

# LAW first_fit_exact: the first fitting reply is exactly the first text reply of 1 to node bytes, errors and empty replies skipped
law first_fit_exact:
  for node: Nat
  for rs: List<&2, C.Reply>
  {C.first_fit(node, rs) == first_fit_spec(node, rs) : Maybe<&2, List<&2, C.W>>}

# LAW read_exact: the replies a line of n calls read are exactly the first n
law read_exact:
  for n: Nat
  for rs: List<&2, C.Reply>
  {C.read(n, rs) == read_spec(n, rs) : List<&2, C.Reply>}

# LAW failures_exact: the failures the cap counts are exactly the failed calls among the outcomes
law failures_exact:
  for os: List<&2, C.Outcome>
  {C.failures(os) == failures_spec(os) : Nat}

def pending_spec(p: C.Pend) -> Bool:
  match p:
    case C.Made{}:
      False{}
    case C.Owed{n}:
      True{}

# LAW pend_pending_exact: the pending check settle_falls reads is exactly: a line owed, not a line built
law pend_pending_exact:
  for p: C.Pend
  {C.Pend.pending(p) == pending_spec(p) : Bool}

# LAW line_open_exact: a line opens with exactly its tries, no call made and no best reply, or with no tries ends at once with the input cut
law line_open_exact:
  for t: Nat
  for n: Nat
  for i: List<&2, C.W>
  {C.line.open(t, n, i) == open_spec(t, n, i) : C.Next}

# LAW line_step_exact: one reply to a line is exactly: with no try left the best (else the input) cut; an error fails the call; an empty reply ends with the best (else the input) cut; a reply within the node's bytes is the line; one not shorter than the best ends with the best cut; the last try ends cut; else the next call goes with one try less, one more call and the reply (its length in bytes) as the best
law line_step_exact:
  for st: C.Lst
  for r: C.Reply
  {C.line.step(st, r) == step_spec(st, r) : C.Next}

# LAW pend_after_exact: a pending line after a call's outcome is exactly: built by a saved line or by the failure with no failures left; one failure fewer after any other failure; unchanged by a disk error or a stop; a built line stays built
law pend_after_exact:
  for p: C.Pend
  for o: C.Outcome
  {C.Pend.after(p, o) == after_spec(p, o) : C.Pend}

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
    case C.Lost{}:
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

# Reader: the requests the entry accepts, read with the wire primitives;
# a request as its numbers: 0 open | 1 a reply | 2 an ended call
type Ask is Data:
  AOpen{t: Nat}
  AStep{l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, r: Maybe<&2, Nat>}
  AAfter{p: C.Pend, o: Nat}

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

def read_open(r: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{AOpen{t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_step.reply(l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Ask>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{AStep{l, m, n, b, x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_step.best(l: Nat, m: Nat, n: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Ask>:
  match r:
    case Wr.Got{b, s}:
      read_step.reply(l, m, n, b, read_m(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_step.node(l: Nat, m: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match r:
    case Wr.Got{n, s}:
      read_step.best(l, m, n, read_m(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_step.made(l: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match r:
    case Wr.Got{m, s}:
      read_step.node(l, m, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_step(r: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match r:
    case Wr.Got{l, s}:
      read_step.made(l, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_after.how.tag(p: C.Pend, t: Nat, s: String) -> Wr.Dec<Ask>:
  match t:
    case 0n:
      Wr.Got{AAfter{p, 0n}, s}
    case 1n:
      Wr.Got{AAfter{p, 1n}, s}
    case 2n:
      Wr.Got{AAfter{p, 2n}, s}
    case 3n:
      Wr.Got{AAfter{p, 3n}, s}
    case 4n+q:
      Wr.Bad{}

def read_after.how(p: C.Pend, r: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match r:
    case Wr.Got{t, s}:
      read_after.how.tag(p, t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_after.owed(r: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match r:
    case Wr.Got{n, s}:
      read_after.how(C.Owed{n}, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_after.tag(t: Nat, s: String) -> Wr.Dec<Ask>:
  match t:
    case 0n:
      read_after.how(C.Made{}, Wr.get_nat(s))
    case 1n:
      read_after.owed(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def read_after(r: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match r:
    case Wr.Got{t, s}:
      read_after.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tag(t: Nat, s: String) -> Wr.Dec<Ask>:
  match t:
    case 0n:
      read_open(Wr.get_nat(s))
    case 1n:
      read_step(Wr.get_nat(s))
    case 2n:
      read_after(Wr.get_nat(s))
    case 3n+p:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: Ask) -> Maybe<&2, Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(r: Wr.Dec<Ask>) -> Maybe<&2, Ask>:
  match r:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

def read_ask.go(r: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match r:
    case Wr.Got{t, s}:
      read_ask.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, Ask>:
  read_ask.whole(read_ask.go(Wr.get_nat(s)))

# LAW line_steps: the steps the shipped compactor takes, driven over the model's replies from a line's open, are `line` itself: every law of `line` holds for them
law line_steps:
  for +tries: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +rs: List<&2, C.Reply>
  {C.line.drive(rs, C.line.open(tries, node, input), node) == C.line(tries, node, input, rs) : C.Line}

# LAW compactor_ffi_open: a line that opens answers the model's line.open, for every node and input (Rust keeps them)
law compactor_ffi_open:
  for +t: Nat
  for node: Nat
  for input: List<&2, C.W>
  for fits: {LawsBase.wire_fits(t) == True{} : Bool}
  {FC.ffi(spell_open(t)) == spell_next(C.line.open(t, node, input)) : String}

# LAW compactor_ffi_step: on every line state and every reply, the entry answers the model's line.step, read from the lengths Rust sends: the same end after the same calls, or the next call with the same tries left, calls made and best reply's length
law compactor_ffi_step:
  for +st: C.Lst
  for +r: C.Reply
  for fits: {step_fits(st, r) == True{} : Bool}
  {FC.ffi(spell_step(st, r)) == spell_next(C.line.step(st, r)) : String}

# LAW compactor_ffi_after: a call of a pending line that ended answers the model's Pend.after
law compactor_ffi_after:
  for +p: C.Pend
  for +o: C.Outcome
  for fits: {pend_fits(p) == True{} : Bool}
  {FC.ffi(spell_after(p, o)) == spell_pend(C.Pend.after(p, o), "") : String}

# LAW compactor_ffi_malformed_exact: every input that is not exactly one request gets exactly the error form 'E ', then "compactor: malformed request"
law compactor_ffi_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, Ask>}
  {FC.ffi(s) == SCon{'E', SCon{' ', "compactor: malformed request"}} : String}

# LAW compactor_ffi_example: anchor: the bytes Rust sends and reads: a line of 5 tries opens; a 700-byte first reply asks again; a 600-byte follow-up on the last try ends cut; a follow-up not shorter ends with the best cut; an empty reply ends with the input cut; an error fails; a reply at the node's size is whole; the last failure left builds a node, a disk error keeps it owed; an unknown tag and input left over are refused
law compactor_ffi_example:
  {FC.ffi("0,5,") == "1,5,0,0," : String} &
  {FC.ffi("1,5,0,512,0,1,700,") == "1,4,1,1,700," : String} &
  {FC.ffi("1,1,4,512,1,700,1,600,") == "0,5,1," : String} &
  {FC.ffi("1,4,1,512,1,700,1,700,") == "0,2,2," : String} &
  {FC.ffi("1,5,0,512,0,1,0,") == "0,1,3," : String} &
  {FC.ffi("1,5,0,512,0,0,") == "0,1,4," : String} &
  {FC.ffi("1,4,1,512,1,700,1,512,") == "0,2,0," : String} &
  {FC.ffi("2,1,0,1,") == "0," : String} &
  {FC.ffi("2,1,2,2,") == "1,2," : String} &
  {FC.ffi("3,") == SCon{'E', SCon{' ', "compactor: malformed request"}} : String} &
  {FC.ffi("0,5,x") == SCon{'E', SCon{' ', "compactor: malformed request"}} : String}

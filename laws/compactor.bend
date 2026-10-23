# eukhe: the laws of area compactor

import Base
import ../bend/compactor.bend as C
import ../bend/optchat/info.bend as OInfo
import ../bend/optchat/node.bend as ONode
import ../bend/optchat/queue.bend as OQueue
import ../bend/optchat/state.bend as OState

# (H1) A compactor call always ends with a line that fits
# -------------------------------------------------------
# docs/harness.md H1, the model in bend/compactor.bend. A reply is free:
# any text, empty, thinking only, an error, missing.

# LAW: a line makes at most `tries` model calls
law line_calls_at_most_tries:
  for +tries: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for rs: List<&2, C.Reply>
  {Nat.is_le(C.Line.calls(C.line(tries, node, input, rs)), tries) == True{} : Bool}

# LAW: with an input that is not empty and a node of at least 4 bytes
# (a character's widest), the line has 1 to node bytes, or the call failed
law line_fits:
  for +tries: Nat
  for +k: Nat
  for +c: C.W
  for +rest: List<&2, C.W>
  for +rs: List<&2, C.Reply>
  {C.line.fits(4n+k, C.Line.line(C.line(tries, 4n+k, c <> rest, rs))) == True{} : Bool}

# LAW: when a reply the line read fits, the line is the first such reply
law line_takes_first_fit:
  for +tries: Nat
  for +node: Nat
  for +input: List<&2, C.W>
  for +rs: List<&2, C.Reply>
  {C.line.first(C.first_fit(node, C.read(C.Line.calls(C.line(tries, node, input, rs)), rs)), C.Line.line(C.line(tries, node, input, rs))) == True{} : Bool}

# LAW: a follow-up not shorter than the best reply ends the line: the
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

# LAW: an empty (or thinking-only) reply is a try, not a failure: the
# line is the input cut to node bytes
law line_empty_is_a_try:
  for t: Nat
  for node: Nat
  for input: List<&2, C.W>
  for rest: List<&2, C.Reply>
  {C.line(1n+t, node, input, C.Says{Nil{}} <> rest) == C.Line{1n, Some{C.cut(input, node)}} : C.Line}

# LAW: a provider error fails the call
law line_error_fails:
  for t: Nat
  for node: Nat
  for input: List<&2, C.W>
  for rest: List<&2, C.Reply>
  {C.line(1n+t, node, input, C.Erred{} <> rest) == C.Line{1n, None{}} : C.Line}

# LAW: a line with n failures left is built once n+1 of its calls failed,
# whatever came between them (disk errors, stops, a saved line)
law fail_cap_builds:
  for n: Nat
  for os: List<&2, C.Outcome>
  for many: {Nat.is_le(1n+n, C.failures(os)) == True{} : Bool}
  {C.Pend.run(os, C.Owed{n}) == C.Made{} : C.Pend}

# (H2) A turn never waits forever for the memory
# ----------------------------------------------
# docs/harness.md H2: the need-first queue of bend/optchat/queue.bend, the settle
# of bend/compactor.bend.

# LAW: while a turn waits, every node the queue starts is a line of the
# view that is not built
law need_first:
  for +cfg: OState.Cfg
  for +s: OState.St
  {C.needed(OState.St.info(s), OState.St.view(s), OQueue.cands.need(cfg, s)) == True{} : Bool}

# LAW: when a turn starts to wait, every call it does not need stops
# (O.St.wait): then every running call and every call the queue starts
# is for a line of the view that is not built
law need_first_running:
  for +cfg: OState.Cfg
  for +s: OState.St
  {C.needed(OState.St.info(s), OState.St.view(s), List.append(&2, ONode.Node, OState.St.busy(OQueue.St.wait(s)), OQueue.cands.need(cfg, OQueue.St.wait(s)))) == True{} : Bool}

# LAW: and it stops no call the view needs: a call of a view line not
# built still runs. Every waiting turn waits for the same view, so no
# turn's wait stops a call another waiting turn needs.
law wait_keeps_needed:
  for +s: OState.St
  {C.kept(OState.St.info(s), OState.St.view(s), OState.St.busy(s), OState.St.busy(OQueue.St.wait(s))) == True{} : Bool}

# LAW: each outcome that counts (a saved line, a failed call) of a
# pending line's call lowers the measure
law settle_falls:
  for +ps: List<&2, C.Pend>
  for +k: Nat
  for +o: C.Outcome
  for due: {C.pending_at(ps, k) == True{} : Bool}
  for lands: {C.Outcome.lands(o) == True{} : Bool}
  {Nat.is_lt(C.measure(C.hit(ps, k, o)), C.measure(ps)) == True{} : Bool}

# LAW: after any outcomes, disk errors and stops among them, those that
# counted for a pending line plus the measure left are at most the
# measure at the start
law settle_bounded:
  for +es: List<&2, C.End>
  for +ps: List<&2, C.Pend>
  {Nat.is_le(Nat.add(C.hits(es, ps), C.measure(C.run(es, ps))), C.measure(ps)) == True{} : Bool}

# LAW: so once as many outcomes as the measure counted for pending lines,
# every line of the view is built
law settle_reached:
  for +es: List<&2, C.End>
  for +ps: List<&2, C.Pend>
  for enough: {Nat.is_le(C.measure(ps), C.hits(es, ps)) == True{} : Bool}
  {C.settled(C.run(es, ps)) == True{} : Bool}

# LAW: when a turn starts to wait, the measure is the failure cap (1+p)
# times the view's unbuilt lines
law settle_start:
  for +p: Nat
  for +info: OInfo.Info
  for +v: List<&2, ONode.Node>
  {C.measure(C.settle.start(p, info, v)) == Nat.mul(C.unbuilt(info, v), 1n+p) : Nat}

# eukhe: the laws of area kin

import Base
import ../bend/kin.bend as K
import ../bend/ffi_kin.bend as FK
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/agents/kin.bend as KinSpec

# (A3) Agent messaging in a tree
# ------------------------------
# bend/kin.bend, run as the compiled core by bend/ffi_kin.bend (eukhe-bend
# rules/kin.rs; asked by the daemon's agent messaging before it routes a
# message). spec/agents/kin.bend states the rule (K1-K4) and the edge
# test (has_edge), admission (admits) and names (mentions).
# Every input is free: any sender, target, columns of edges and state.
#
# R1: the decision on a message is the one K1-K3 state: an agent messages
#     only its parent and its own children, never itself; a message to
#     itself is refused as such, one to no kin as not kin, and the parent
#     relation is named when both edges hold.
# R2: the landing is the one K4 states: busy queues, idle delivers, parked
#     wakes then delivers (no landing drops the message: the type Landing
#     has no drop).
# R3: the entry answers each request Rust writes (tag 0: the sender, the
#     target, the children and the parents as List<String>; tag 1: the
#     state; every length within the wire) with the core's decision (0
#     then the relation | 1 then the refusal's text) or landing, reads
#     exactly the request and nothing after it, and answers any other
#     input with the exact error form `E kin: malformed request`.

# Spec helpers
# ------------

# a verdict admits
def kin_admitted(v: K.Verdict) -> Bool:
  match v:
    case K.Admit{r}:
      True{}
    case K.Refuse{f}:
      False{}

# R1: the edge a relation names holds: a parent is linked from the sender,
# a child to it
def kin_rel_holds(r: K.Relation, +s: String, +t: String, cs: List<&2, String>, ps: List<&2, String>) -> Bool:
  match r:
    case K.Parent{}:
      KinSpec.has_edge(cs, ps, s, t)
    case K.Child{}:
      KinSpec.has_edge(cs, ps, t, s)

# R1: the text of a refusal, as Rust's callers read it
def kin_text(f: K.Refusal) -> String:
  match f:
    case K.SelfMessage{}:
      "an agent cannot message itself"
    case K.NotKin{}:
      "agents message only their parent and their own children"

# R3: the spelling of a request and of its reply

def kin_state_code(st: K.State) -> Nat:
  match st:
    case K.Busy{}:
      0n
    case K.Idle{}:
      1n
    case K.Parked{}:
      2n

def kin_rel_code(r: K.Relation) -> Nat:
  match r:
    case K.Parent{}:
      0n
    case K.Child{}:
      1n

def kin_land_code(l: K.Landing) -> Nat:
  match l:
    case K.Queue{}:
      0n
    case K.Deliver{}:
      1n
    case K.WakeThenDeliver{}:
      2n

def kin_w_req(q: FK.Req, rest: String) -> String:
  match q:
    case FK.QAdmit{s, t, cs, ps}:
      Wr.put_nat(0n, Wr.put_str(s, Wr.put_str(t, Wr.put_list(~String, ~Wr.put_str, cs, Wr.put_list(~String, ~Wr.put_str, ps, rest)))))
    case FK.QLand{st}:
      Wr.put_nat(1n, Wr.put_nat(kin_state_code(st), rest))

def kin_w_verdict(v: K.Verdict) -> String:
  match v:
    case K.Admit{r}:
      Wr.put_nat(0n, Wr.put_nat(kin_rel_code(r), ""))
    case K.Refuse{f}:
      Wr.put_nat(1n, Wr.put_str(kin_text(f), ""))

def kin_w_reply(q: FK.Req) -> String:
  match q:
    case FK.QAdmit{s, t, cs, ps}:
      kin_w_verdict(K.decide(s, t, cs, ps))
    case FK.QLand{st}:
      Wr.put_nat(kin_land_code(K.land(st)), "")

# every length of xs fits the wire
def kin_fit_strs(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(LawsBase.wire_fits(String.length(x)), kin_fit_strs(t))

# every length and count of the request fits the wire
def kin_fit_req(q: FK.Req) -> Bool:
  match q:
    case FK.QAdmit{s, t, +cs, +ps}:
      Bool.and(LawsBase.wire_fits(String.length(s)), Bool.and(LawsBase.wire_fits(String.length(t)), Bool.and(LawsBase.wire_fits(List.length(&2, String, cs)), Bool.and(kin_fit_strs(cs), Bool.and(LawsBase.wire_fits(List.length(&2, String, ps)), kin_fit_strs(ps))))))
    case FK.QLand{st}:
      True{}

# Laws: the decision (R1)
# -----------------------

# LAW kin_parent_first (A3, R1, K3): a message to another agent t that
# the edge from the sender s to t links (spec has_edge: t is s's parent)
# is admitted as to the parent, also when the edge from t to s holds too
# EXCLUDES: a child named when the parent link holds too, a message to
#   the parent refused, the edge read the other way round
law kin_parent_first:
  for +s: String
  for +t: String
  for +cs: List<&2, String>
  for +ps: List<&2, String>
  for other: {String.eq(s, t) == False{} : Bool}
  for up: {KinSpec.has_edge(cs, ps, s, t) == True{} : Bool}
  {K.decide(s, t, cs, ps) == K.Admit{K.Parent{}} : K.Verdict}

# LAW kin_not_kin_refused (A3, R1, K3): a message to another agent that
# the spec does not admit (no edge either way: spec admits false) is
# refused as not kin
# EXCLUDES: a refusal to no kin named as a self message, a sibling or
#   another tree refused with another text
law kin_not_kin_refused:
  for +s: String
  for +t: String
  for +cs: List<&2, String>
  for +ps: List<&2, String>
  for other: {String.eq(s, t) == False{} : Bool}
  for no: {KinSpec.admits(s, t, cs, ps) == False{} : Bool}
  {K.decide(s, t, cs, ps) == K.Refuse{K.NotKin{}} : K.Verdict}

# LAW kin_admit_iff (A3, R1, K2, K3): a message is admitted exactly when
# the sender is not the target and a direct edge links them, either way
# EXCLUDES: a message to itself, to a sibling, a grandparent, a grandchild
#   or another tree admitted; a message to the parent or a child refused
law kin_admit_iff:
  for +s: String
  for +t: String
  for +cs: List<&2, String>
  for +ps: List<&2, String>
  {kin_admitted(K.decide(s, t, cs, ps)) == KinSpec.admits(s, t, cs, ps) : Bool}

# LAW kin_no_cross_tree (A3, R1, K3): with the edges two trees A ++ B
# (A's columns of one length), a sender named nowhere in B and a target
# named nowhere in A, the message is refused: no message crosses trees
# EXCLUDES: an edge read across the seam of A and B (the columns paired
#   off by one), a message admitted between two trees, an edge matched on
#   one end only
law kin_no_cross_tree:
  for +s: String
  for +t: String
  for +ca: List<&2, String>
  for +pa: List<&2, String>
  for +cb: List<&2, String>
  for +pb: List<&2, String>
  for hl: {List.length(&2, String, ca) == List.length(&2, String, pa) : Nat}
  for h1: {KinSpec.mentions(cb, s) == False{} : Bool}
  for h2: {KinSpec.mentions(pb, s) == False{} : Bool}
  for h3: {KinSpec.mentions(ca, t) == False{} : Bool}
  for h4: {KinSpec.mentions(pa, t) == False{} : Bool}
  {kin_admitted(K.decide(s, t, List.append(&2, String, ca, cb), List.append(&2, String, pa, pb))) == False{} : Bool}

# LAW kin_no_self (A3, R1, K2): a message from an agent to itself is
# refused as such, whatever the tree (also a tree with a self loop)
# EXCLUDES: a self message admitted through a self loop, refused with
#   another text
law kin_no_self:
  for +s: String
  for +cs: List<&2, String>
  for +ps: List<&2, String>
  {K.decide(s, s, cs, ps) == K.Refuse{K.SelfMessage{}} : K.Verdict}

# LAW kin_relation_exact (A3, R1, K3): an admitted message names the edge
# that admits it: a parent is linked from the sender to the target, a
# child from the target to the sender
# EXCLUDES: a parent named for a child, a relation named with no edge
law kin_relation_exact:
  for +s: String
  for +t: String
  for +cs: List<&2, String>
  for +ps: List<&2, String>
  for +r: K.Relation
  for e: {K.decide(s, t, cs, ps) == K.Admit{r} : K.Verdict}
  {kin_rel_holds(r, s, t, cs, ps) == True{} : Bool}

# LAW kin_text_spec (A3, R1): every refusal text is the spec's
# EXCLUDES: a changed text, the two texts swapped
law kin_text_spec:
  for +f: K.Refusal
  {K.text(f) == kin_text(f) : String}

# LAW kin_example (A3, R1): anchor: the tree and messages of Rust's test
# `the_core_decides_who_may_message_whom` (crates/eukhe-bend/src/rules/
# kin.rs; root named r): root -> a, root -> b, a -> c and y -> x: a child
# to its parent, a parent to its child, a sibling, a grandchild to its
# grandparent, a message to itself, another tree; and an edge past the
# shorter column
# EXCLUDES: a decision other than the one that Rust test reads
law kin_example:
  {[K.decide("a", "r", ["a", "b", "c"], ["r", "r", "a"]), K.decide("r", "a", ["a", "b", "c"], ["r", "r", "a"]), K.decide("a", "b", ["a", "b", "c"], ["r", "r", "a"]), K.decide("c", "r", ["a", "b", "c"], ["r", "r", "a"]), K.decide("a", "a", ["a", "b", "c"], ["r", "r", "a"]), K.decide("x", "a", ["a", "b", "c", "x"], ["r", "r", "a", "y"]), K.decide("c", "a", ["a", "b", "c"], ["r", "r"])] == [K.Admit{K.Parent{}}, K.Admit{K.Child{}}, K.Refuse{K.NotKin{}}, K.Refuse{K.NotKin{}}, K.Refuse{K.SelfMessage{}}, K.Refuse{K.NotKin{}}, K.Refuse{K.NotKin{}}] : List<&2, K.Verdict>}

# Laws: the landing (R2)
# ----------------------

# LAW kin_land_table_example (A3, R2, K4): anchor: the landing of every
# state, as Rust's test `the_core_lands_a_message_in_every_state`
# (crates/eukhe-bend/src/rules/kin.rs) reads it: busy queues, idle
# delivers, parked wakes then delivers
# EXCLUDES: a parked target left asleep with the message, a busy target
#   interrupted, an idle target woken
law kin_land_table_example:
  {[K.land(K.Busy{}), K.land(K.Idle{}), K.land(K.Parked{})] == [K.Queue{}, K.Deliver{}, K.WakeThenDeliver{}] : List<&2, K.Landing>}

# Laws: the entry (R3)
# --------------------

# LAW kin_entry_answers (A3, R3): the entry answers every request Rust
# spells, every length within the wire, with the core's decision or
# landing spelled (kin_w_reply)
# EXCLUDES: fields read in another order, the children and the parents
#   swapped, an edge lost, one request answered for the other, a default
law kin_entry_answers:
  for +q: FK.Req
  for fit: {kin_fit_req(q) == True{} : Bool}
  {FK.ffi(kin_w_req(q, "")) == kin_w_reply(q) : String}

# LAW kin_entry_left_over (A3, R3): a spelled request followed by more
# input answers the error form
# EXCLUDES: the input after the request ignored or read into a field
law kin_entry_left_over:
  for +q: FK.Req
  for +ch: Char
  for +t: String
  for fit: {kin_fit_req(q) == True{} : Bool}
  {FK.ffi(kin_w_req(q, SCon{ch, t})) == Wr.err("kin: malformed request") : String}

# LAW kin_entry_reads (A3, R3): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown tag or
#   state, a short field, a list shorter than its count, input left over)
law kin_entry_reads:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FK.ffi(s)) == False{} : Bool}
  exs q: FK.Req
  {s == kin_w_req(q, "") : String} & {kin_fit_req(q) == True{} : Bool}

# LAW kin_entry_malformed_exact (A3, R3): every error the entry answers is
# exactly `E kin: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law kin_entry_malformed_exact:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FK.ffi(s)) == True{} : Bool}
  {FK.ffi(s) == Wr.err("kin: malformed request") : String}

# LAW kin_entry_example (A3, R3): anchor: the wire strings Rust sends and
# the replies it reads; an unknown state, an unknown tag, input left over
# EXCLUDES: another spelling of a request or of a reply
law kin_entry_example:
  {[FK.ffi("0,1,a1,r2,1,a1,b2,1,r1,r"), FK.ffi("0,1,r1,a2,1,a1,b2,1,r1,r"), FK.ffi("0,1,a1,b2,1,a1,b2,1,r1,r"), FK.ffi("0,1,a1,a0,0,"), FK.ffi("1,0,"), FK.ffi("1,1,"), FK.ffi("1,2,"), FK.ffi("1,3,"), FK.ffi("2,"), FK.ffi("1,0,x")] == ["0,0,", "0,1,", "1,55,agents message only their parent and their own children", "1,30,an agent cannot message itself", "0,", "1,", "2,", Wr.err("kin: malformed request"), Wr.err("kin: malformed request"), Wr.err("kin: malformed request")] : List<&2, String>}

# ffi_verify: the compiled Bend core's entry for verified completion
# (bend/verify.bend). Rust `eukhe_bend::rules::verify` calls it through
# `eukhe_bend::call` from eukhe-core durable/acceptance (every decision of
# the verifier) and eukhe-cli print_runtime (the exit code of a headless
# run).
#
# Request (crates/eukhe-bend/WIRE.md): a tag, then its fields.
#   0 act:     who, the act, the acceptance
#   1 advance: the state now (Nat), the cap of returns in a row (Nat), the
#              acceptance
#   2 label:   the state now, the slots (List<Slot>)
#   3 exit:    the run's own exit code (Nat), the state now, the slots
#   4 command: the expected exit code (Nat), whether the protected files
#              are intact (Bool), the evidence
#   5 until:   the evidence
#   6 judge:   the judge's answer
#   7 claims:  held, checked, goal, claimed, ended (five Bools)
# Who: 0 the owner, 1 the worker, 2 the verifier. An act: 0 assign (the
# number of checks, a Nat), 1 claim, 2 record (the revision, the index,
# the verdict, the state it judged). An acceptance: the revision (Nat),
# the slots (List<Slot>), claimed (Bool), the tries (Nat). A slot: 0 open,
# 1 judged (the verdict, then the state it judged, a Nat). A verdict: 0
# confirmed, 1 refuted, 2 broken, 3 unjudged. Evidence: 0 exited (then the
# code, a Nat), 1 no status, 2 timed out, 3 could not start, 4 cancelled.
# An answer: 0 yes, 1 no, 2 unreadable, 3 unavailable, 4 stopped.
# Reply: act: admitted (Bool), then the acceptance; advance: the action (0
# rest, 1 run then the index, 2 return, 3 end then the label), then the
# acceptance; label: 0 verified, 1 failed, 2 unverified; exit: the code
# (Nat); command, until, judge: the verdict; claims: whether the final
# answer is a claim (Bool).
# Any other input (an unknown tag, a malformed field, input left after the
# request) answers the error form "verify: malformed request", never a
# default. laws/verify.bend (section entry) states this file's laws. Pure:
# no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./verify.bend as V

# A request of the entry
type Req is Data:
  QAct{who: V.Actor, op: V.Op, a: V.Acc}
  QAdvance{now: Nat, cap: Nat, a: V.Acc}
  QLabel{now: Nat, slots: List<&2, V.Slot>}
  QExit{base: Nat, now: Nat, slots: List<&2, V.Slot>}
  QCommand{expect: Nat, intact: Bool, ev: V.Evidence}
  QUntil{ev: V.Evidence}
  QJudge{ans: V.Answer}
  QClaims{held: Bool, checked: Bool, goal: Bool, claimed: Bool, ended: Bool}

# Decoders
# --------

def get_verdict(r: W.Dec<Nat>) -> W.Dec<V.Verdict>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{V.Confirmed{}, s}
        case 1n:
          W.Got{V.Refuted{}, s}
        case 2n:
          W.Got{V.Broken{}, s}
        case 3n:
          W.Got{V.Unjudged{}, s}
        case 4n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_slot.at(v: V.Verdict, r: W.Dec<Nat>) -> W.Dec<V.Slot>:
  match r:
    case W.Got{at, s}:
      W.Got{V.Judged{v, at}, s}
    case W.Bad{}:
      W.Bad{}

def get_slot.verdict(r: W.Dec<V.Verdict>) -> W.Dec<V.Slot>:
  match r:
    case W.Got{v, s}:
      get_slot.at(v, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_slot.tag(r: W.Dec<Nat>) -> W.Dec<V.Slot>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{V.Open{}, s}
        case 1n:
          get_slot.verdict(get_verdict(W.get_nat(s)))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the slot at the start of s
def get_slot(s: String) -> W.Dec<V.Slot>:
  get_slot.tag(W.get_nat(s))

# the slots at the start of s
def get_slots(s: String) -> W.Dec<List<&2, V.Slot>>:
  W.get_list(~V.Slot, ~get_slot, s)

def get_acc.tries(rev: Nat, slots: List<&2, V.Slot>, claimed: Bool, r: W.Dec<Nat>) -> W.Dec<V.Acc>:
  match r:
    case W.Got{tries, s}:
      W.Got{V.Acc{rev, slots, claimed, tries}, s}
    case W.Bad{}:
      W.Bad{}

def get_acc.claimed(rev: Nat, slots: List<&2, V.Slot>, r: W.Dec<Bool>) -> W.Dec<V.Acc>:
  match r:
    case W.Got{claimed, s}:
      get_acc.tries(rev, slots, claimed, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_acc.slots(rev: Nat, r: W.Dec<List<&2, V.Slot>>) -> W.Dec<V.Acc>:
  match r:
    case W.Got{slots, s}:
      get_acc.claimed(rev, slots, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_acc.rev(r: W.Dec<Nat>) -> W.Dec<V.Acc>:
  match r:
    case W.Got{rev, s}:
      get_acc.slots(rev, get_slots(s))
    case W.Bad{}:
      W.Bad{}

# the acceptance at the start of s
def get_acc(s: String) -> W.Dec<V.Acc>:
  get_acc.rev(W.get_nat(s))

def get_actor(r: W.Dec<Nat>) -> W.Dec<V.Actor>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{V.Owner{}, s}
        case 1n:
          W.Got{V.Worker{}, s}
        case 2n:
          W.Got{V.Verifier{}, s}
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_evidence.code(r: W.Dec<Nat>) -> W.Dec<V.Evidence>:
  match r:
    case W.Got{code, s}:
      W.Got{V.Exited{code}, s}
    case W.Bad{}:
      W.Bad{}

def get_evidence(r: W.Dec<Nat>) -> W.Dec<V.Evidence>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_evidence.code(W.get_nat(s))
        case 1n:
          W.Got{V.NoStatus{}, s}
        case 2n:
          W.Got{V.TimedOut{}, s}
        case 3n:
          W.Got{V.SpawnFailed{}, s}
        case 4n:
          W.Got{V.Cancelled{}, s}
        case 5n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_answer(r: W.Dec<Nat>) -> W.Dec<V.Answer>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{V.Yes{}, s}
        case 1n:
          W.Got{V.No{}, s}
        case 2n:
          W.Got{V.Unreadable{}, s}
        case 3n:
          W.Got{V.Unavailable{}, s}
        case 4n:
          W.Got{V.Stopped{}, s}
        case 5n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_op.assign(r: W.Dec<Nat>) -> W.Dec<V.Op>:
  match r:
    case W.Got{n, s}:
      W.Got{V.Assign{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_op.at(rev: Nat, i: Nat, v: V.Verdict, r: W.Dec<Nat>) -> W.Dec<V.Op>:
  match r:
    case W.Got{at, s}:
      W.Got{V.Record{rev, i, v, at}, s}
    case W.Bad{}:
      W.Bad{}

def get_op.verdict(rev: Nat, i: Nat, r: W.Dec<V.Verdict>) -> W.Dec<V.Op>:
  match r:
    case W.Got{v, s}:
      get_op.at(rev, i, v, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_op.index(rev: Nat, r: W.Dec<Nat>) -> W.Dec<V.Op>:
  match r:
    case W.Got{i, s}:
      get_op.verdict(rev, i, get_verdict(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_op.rev(r: W.Dec<Nat>) -> W.Dec<V.Op>:
  match r:
    case W.Got{rev, s}:
      get_op.index(rev, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_op(r: W.Dec<Nat>) -> W.Dec<V.Op>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_op.assign(W.get_nat(s))
        case 1n:
          W.Got{V.Claim{}, s}
        case 2n:
          get_op.rev(W.get_nat(s))
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_req.act_a(who: V.Actor, op: V.Op, r: W.Dec<V.Acc>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QAct{who, op, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.act_op(who: V.Actor, r: W.Dec<V.Op>) -> W.Dec<Req>:
  match r:
    case W.Got{op, s}:
      get_req.act_a(who, op, get_acc(s))
    case W.Bad{}:
      W.Bad{}

def get_req.act(r: W.Dec<V.Actor>) -> W.Dec<Req>:
  match r:
    case W.Got{who, s}:
      get_req.act_op(who, get_op(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.advance_a(now: Nat, cap: Nat, r: W.Dec<V.Acc>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QAdvance{now, cap, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.advance_cap(now: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{cap, s}:
      get_req.advance_a(now, cap, get_acc(s))
    case W.Bad{}:
      W.Bad{}

def get_req.advance(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_req.advance_cap(now, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.label_s(now: Nat, r: W.Dec<List<&2, V.Slot>>) -> W.Dec<Req>:
  match r:
    case W.Got{slots, s}:
      W.Got{QLabel{now, slots}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.label(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_req.label_s(now, get_slots(s))
    case W.Bad{}:
      W.Bad{}

def get_req.exit_s(base: Nat, now: Nat, r: W.Dec<List<&2, V.Slot>>) -> W.Dec<Req>:
  match r:
    case W.Got{slots, s}:
      W.Got{QExit{base, now, slots}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.exit_now(base: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_req.exit_s(base, now, get_slots(s))
    case W.Bad{}:
      W.Bad{}

def get_req.exit(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{base, s}:
      get_req.exit_now(base, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.command_ev(expect: Nat, intact: Bool, r: W.Dec<V.Evidence>) -> W.Dec<Req>:
  match r:
    case W.Got{ev, s}:
      W.Got{QCommand{expect, intact, ev}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.command_intact(expect: Nat, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{intact, s}:
      get_req.command_ev(expect, intact, get_evidence(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.command(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{expect, s}:
      get_req.command_intact(expect, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.until(r: W.Dec<V.Evidence>) -> W.Dec<Req>:
  match r:
    case W.Got{ev, s}:
      W.Got{QUntil{ev}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.judge(r: W.Dec<V.Answer>) -> W.Dec<Req>:
  match r:
    case W.Got{ans, s}:
      W.Got{QJudge{ans}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.claims_e(held: Bool, checked: Bool, goal: Bool, claimed: Bool, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{ended, s}:
      W.Got{QClaims{held, checked, goal, claimed, ended}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.claims_c(held: Bool, checked: Bool, goal: Bool, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{claimed, s}:
      get_req.claims_e(held, checked, goal, claimed, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.claims_g(held: Bool, checked: Bool, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{goal, s}:
      get_req.claims_c(held, checked, goal, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.claims_k(held: Bool, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{checked, s}:
      get_req.claims_g(held, checked, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.claims(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{held, s}:
      get_req.claims_k(held, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

# the request whose tag r read
def get_req(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_req.act(get_actor(W.get_nat(s)))
        case 1n:
          get_req.advance(W.get_nat(s))
        case 2n:
          get_req.label(W.get_nat(s))
        case 3n:
          get_req.exit(W.get_nat(s))
        case 4n:
          get_req.command(W.get_nat(s))
        case 5n:
          get_req.until(get_evidence(W.get_nat(s)))
        case 6n:
          get_req.judge(get_answer(W.get_nat(s)))
        case 7n:
          get_req.claims(W.get_bool(s))
        case 8n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# Encoders
# --------

def put_verdict(v: V.Verdict, rest: String) -> String:
  match v:
    case V.Confirmed{}:
      W.put_nat(0n, rest)
    case V.Refuted{}:
      W.put_nat(1n, rest)
    case V.Broken{}:
      W.put_nat(2n, rest)
    case V.Unjudged{}:
      W.put_nat(3n, rest)

def put_slot(x: V.Slot, rest: String) -> String:
  match x:
    case V.Open{}:
      W.put_nat(0n, rest)
    case V.Judged{v, at}:
      W.put_nat(1n, put_verdict(v, W.put_nat(at, rest)))

def put_acc(a: V.Acc, rest: String) -> String:
  match a:
    case V.Acc{rev, slots, claimed, tries}:
      W.put_nat(rev, W.put_list(~V.Slot, ~put_slot, slots, W.put_bool(claimed, W.put_nat(tries, rest))))

def put_label(l: V.Label, rest: String) -> String:
  match l:
    case V.Verified{}:
      W.put_nat(0n, rest)
    case V.Failed{}:
      W.put_nat(1n, rest)
    case V.Unverified{}:
      W.put_nat(2n, rest)

def put_action(x: V.Action, rest: String) -> String:
  match x:
    case V.Rest{}:
      W.put_nat(0n, rest)
    case V.Run{i}:
      W.put_nat(1n, W.put_nat(i, rest))
    case V.Return{}:
      W.put_nat(2n, rest)
    case V.End{l}:
      W.put_nat(3n, put_label(l, rest))

def put_acted(r: Bool & V.Acc) -> String:
  (ok, a) = r
  W.put_bool(ok, put_acc(a, ""))

def put_advanced(r: V.Action & V.Acc) -> String:
  (x, a) = r
  put_action(x, put_acc(a, ""))

# the reply of a request: the model's decision, encoded
def answer(q: Req) -> String:
  match q:
    case QAct{who, op, a}:
      put_acted(V.act(who, op, a))
    case QAdvance{now, cap, a}:
      put_advanced(V.advance(now, cap, a))
    case QLabel{now, slots}:
      put_label(V.label(now, slots), "")
    case QExit{base, now, slots}:
      W.put_nat(V.exit(base, now, slots), "")
    case QCommand{expect, intact, ev}:
      put_verdict(V.grade_command(expect, intact, ev), "")
    case QUntil{ev}:
      put_verdict(V.grade_until(ev), "")
    case QJudge{ans}:
      put_verdict(V.grade_judge(ans), "")
    case QClaims{held, checked, goal, claimed, ended}:
      W.put_bool(V.claims(held, checked, goal, claimed, ended), "")

# The entry
# ---------

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("verify: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("verify: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(W.get_nat(input)))

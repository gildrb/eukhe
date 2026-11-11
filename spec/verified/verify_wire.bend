# verified (spec): the wire of the verified-completion entry
# (bend/ffi_verify.bend) as the laws of area verify (laws/verify.bend,
# section entry) read it: the requests and replies spelled with the wire
# primitives only (bend/wire.bend; their round trips: laws/wire.bend),
# what fits the wire, and the reader of a request. A spec: the shipped
# code never calls it.

import Base
import ../../bend/verify.bend as V
import ../../bend/ffi_verify.bend as FV
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase

# Spellers: a request as Rust writes it
# -------------------------------------

# the tag of a verdict: 0 confirmed, 1 refuted, 2 broken, 3 unjudged
def w_verdict(v: V.Verdict) -> Nat:
  match v:
    case V.Confirmed{}:
      0n
    case V.Refuted{}:
      1n
    case V.Broken{}:
      2n
    case V.Unjudged{}:
      3n

# a slot: 0 open; 1 judged, the verdict, the state it judged
def w_slot(x: V.Slot, rest: String) -> String:
  match x:
    case V.Open{}:
      Wr.put_nat(0n, rest)
    case V.Judged{v, at}:
      Wr.put_nat(1n, Wr.put_nat(w_verdict(v), Wr.put_nat(at, rest)))

def w_slots(xs: List<&2, V.Slot>, rest: String) -> String:
  Wr.put_list(~V.Slot, ~w_slot, xs, rest)

# an acceptance: the revision, the slots, claimed, the tries
def w_acc(a: V.Acc, rest: String) -> String:
  match a:
    case V.Acc{rev, slots, claimed, tries}:
      Wr.put_nat(rev, w_slots(slots, Wr.put_bool(claimed, Wr.put_nat(tries, rest))))

# the tag of an actor: 0 the owner, 1 the worker, 2 the verifier
def w_actor(who: V.Actor) -> Nat:
  match who:
    case V.Owner{}:
      0n
    case V.Worker{}:
      1n
    case V.Verifier{}:
      2n

# an act: 0 assign and the number of checks; 1 claim; 2 record, the
# revision, the index, the verdict, the state it judged
def w_op(op: V.Op, rest: String) -> String:
  match op:
    case V.Assign{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case V.Claim{}:
      Wr.put_nat(1n, rest)
    case V.Record{of, i, v, at}:
      Wr.put_nat(2n, Wr.put_nat(of, Wr.put_nat(i, Wr.put_nat(w_verdict(v), Wr.put_nat(at, rest)))))

# evidence: 0 exited and the code; 1 no status; 2 timed out; 3 could not
# start; 4 cancelled
def w_evidence(ev: V.Evidence, rest: String) -> String:
  match ev:
    case V.Exited{code}:
      Wr.put_nat(0n, Wr.put_nat(code, rest))
    case V.NoStatus{}:
      Wr.put_nat(1n, rest)
    case V.TimedOut{}:
      Wr.put_nat(2n, rest)
    case V.SpawnFailed{}:
      Wr.put_nat(3n, rest)
    case V.Cancelled{}:
      Wr.put_nat(4n, rest)

# the tag of an answer: 0 yes, 1 no, 2 unreadable, 3 unavailable, 4
# stopped
def w_answer(ans: V.Answer) -> Nat:
  match ans:
    case V.Yes{}:
      0n
    case V.No{}:
      1n
    case V.Unreadable{}:
      2n
    case V.Unavailable{}:
      3n
    case V.Stopped{}:
      4n

# a request, then rest
def w_req(q: FV.Req, rest: String) -> String:
  match q:
    case FV.QAct{who, op, a}:
      Wr.put_nat(0n, Wr.put_nat(w_actor(who), w_op(op, w_acc(a, rest))))
    case FV.QAdvance{now, cap, a}:
      Wr.put_nat(1n, Wr.put_nat(now, Wr.put_nat(cap, w_acc(a, rest))))
    case FV.QLabel{now, slots}:
      Wr.put_nat(2n, Wr.put_nat(now, w_slots(slots, rest)))
    case FV.QExit{base, now, slots}:
      Wr.put_nat(3n, Wr.put_nat(base, Wr.put_nat(now, w_slots(slots, rest))))
    case FV.QCommand{expect, intact, ev}:
      Wr.put_nat(4n, Wr.put_nat(expect, Wr.put_bool(intact, w_evidence(ev, rest))))
    case FV.QUntil{ev}:
      Wr.put_nat(5n, w_evidence(ev, rest))
    case FV.QJudge{ans}:
      Wr.put_nat(6n, Wr.put_nat(w_answer(ans), rest))
    case FV.QClaims{held, checked, goal, claimed, ended}:
      Wr.put_nat(7n, Wr.put_bool(held, Wr.put_bool(checked, Wr.put_bool(goal, Wr.put_bool(claimed, Wr.put_bool(ended, rest))))))

# Spellers: the reply, as Rust reads it
# -------------------------------------

# the tag of a label: 0 verified, 1 failed, 2 unverified
def w_label(l: V.Label) -> Nat:
  match l:
    case V.Verified{}:
      0n
    case V.Failed{}:
      1n
    case V.Unverified{}:
      2n

# an action: 0 rest; 1 run and the index; 2 return; 3 end and the label
def w_action(x: V.Action, rest: String) -> String:
  match x:
    case V.Rest{}:
      Wr.put_nat(0n, rest)
    case V.Run{i}:
      Wr.put_nat(1n, Wr.put_nat(i, rest))
    case V.Return{}:
      Wr.put_nat(2n, rest)
    case V.End{l}:
      Wr.put_nat(3n, Wr.put_nat(w_label(l), rest))

def w_acted(r: Bool & V.Acc) -> String:
  (ok, a) = r
  Wr.put_bool(ok, w_acc(a, ""))

def w_advanced(r: V.Action & V.Acc) -> String:
  (x, a) = r
  w_action(x, w_acc(a, ""))

# the reply to a request: the model's decision, spelled as Rust reads it.
# The decisions are the model's (bend/verify.bend), each pinned by the
# laws of laws/verify.bend: act by the laws of R3, advance by the laws of
# R4, label by verify_label_is_spec, exit by verify_exit_is_spec, the
# verdicts by the laws of R1, claims by the laws of R7
def w_reply(q: FV.Req) -> String:
  match q:
    case FV.QAct{who, op, a}:
      w_acted(V.act(who, op, a))
    case FV.QAdvance{now, cap, a}:
      w_advanced(V.advance(now, cap, a))
    case FV.QLabel{now, slots}:
      Wr.put_nat(w_label(V.label(now, slots)), "")
    case FV.QExit{base, now, slots}:
      Wr.put_nat(V.exit(base, now, slots), "")
    case FV.QCommand{expect, intact, ev}:
      Wr.put_nat(w_verdict(V.grade_command(expect, intact, ev)), "")
    case FV.QUntil{ev}:
      Wr.put_nat(w_verdict(V.grade_until(ev)), "")
    case FV.QJudge{ans}:
      Wr.put_nat(w_verdict(V.grade_judge(ans)), "")
    case FV.QClaims{held, checked, goal, claimed, ended}:
      Wr.put_bool(V.claims(held, checked, goal, claimed, ended), "")

# Bounds: every number of a request fits the wire
# -----------------------------------------------

def fit_slot(x: V.Slot) -> Bool:
  match x:
    case V.Open{}:
      True{}
    case V.Judged{v, at}:
      LawsBase.wire_fits(at)

def fit_slots.items(xs: List<&2, V.Slot>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(fit_slot(x), fit_slots.items(t))

# the count of the slots and every slot fit the wire
def fit_slots(+xs: List<&2, V.Slot>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, V.Slot, xs)), fit_slots.items(xs))

def fit_acc(a: V.Acc) -> Bool:
  match a:
    case V.Acc{rev, slots, claimed, tries}:
      Bool.and(LawsBase.wire_fits(rev), Bool.and(fit_slots(slots), LawsBase.wire_fits(tries)))

def fit_op(op: V.Op) -> Bool:
  match op:
    case V.Assign{n}:
      LawsBase.wire_fits(n)
    case V.Claim{}:
      True{}
    case V.Record{of, i, v, at}:
      Bool.and(LawsBase.wire_fits(of), Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(at)))

def fit_evidence(ev: V.Evidence) -> Bool:
  match ev:
    case V.Exited{code}:
      LawsBase.wire_fits(code)
    case V.NoStatus{}:
      True{}
    case V.TimedOut{}:
      True{}
    case V.SpawnFailed{}:
      True{}
    case V.Cancelled{}:
      True{}

def fit_req(q: FV.Req) -> Bool:
  match q:
    case FV.QAct{who, op, a}:
      Bool.and(fit_op(op), fit_acc(a))
    case FV.QAdvance{now, cap, a}:
      Bool.and(LawsBase.wire_fits(now), Bool.and(LawsBase.wire_fits(cap), fit_acc(a)))
    case FV.QLabel{now, slots}:
      Bool.and(LawsBase.wire_fits(now), fit_slots(slots))
    case FV.QExit{base, now, slots}:
      Bool.and(LawsBase.wire_fits(base), Bool.and(LawsBase.wire_fits(now), fit_slots(slots)))
    case FV.QCommand{expect, intact, ev}:
      Bool.and(LawsBase.wire_fits(expect), fit_evidence(ev))
    case FV.QUntil{ev}:
      fit_evidence(ev)
    case FV.QJudge{ans}:
      True{}
    case FV.QClaims{held, checked, goal, claimed, ended}:
      True{}

# The reader: the request an input spells, read with the wire's decoders
# ----------------------------------------------------------------------

def r_verdict(r: Wr.Dec<Nat>) -> Wr.Dec<V.Verdict>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{V.Confirmed{}, s}
        case 1n:
          Wr.Got{V.Refuted{}, s}
        case 2n:
          Wr.Got{V.Broken{}, s}
        case 3n:
          Wr.Got{V.Unjudged{}, s}
        case 4n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_slot.at(v: V.Verdict, r: Wr.Dec<Nat>) -> Wr.Dec<V.Slot>:
  match r:
    case Wr.Got{at, s}:
      Wr.Got{V.Judged{v, at}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_slot.verdict(r: Wr.Dec<V.Verdict>) -> Wr.Dec<V.Slot>:
  match r:
    case Wr.Got{v, s}:
      r_slot.at(v, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_slot.tag(r: Wr.Dec<Nat>) -> Wr.Dec<V.Slot>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{V.Open{}, s}
        case 1n:
          r_slot.verdict(r_verdict(Wr.get_nat(s)))
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_slot(s: String) -> Wr.Dec<V.Slot>:
  r_slot.tag(Wr.get_nat(s))

def r_slots(s: String) -> Wr.Dec<List<&2, V.Slot>>:
  Wr.get_list(~V.Slot, ~r_slot, s)

def r_acc.tries(rev: Nat, slots: List<&2, V.Slot>, claimed: Bool, r: Wr.Dec<Nat>) -> Wr.Dec<V.Acc>:
  match r:
    case Wr.Got{tries, s}:
      Wr.Got{V.Acc{rev, slots, claimed, tries}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_acc.claimed(rev: Nat, slots: List<&2, V.Slot>, r: Wr.Dec<Bool>) -> Wr.Dec<V.Acc>:
  match r:
    case Wr.Got{claimed, s}:
      r_acc.tries(rev, slots, claimed, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_acc.slots(rev: Nat, r: Wr.Dec<List<&2, V.Slot>>) -> Wr.Dec<V.Acc>:
  match r:
    case Wr.Got{slots, s}:
      r_acc.claimed(rev, slots, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_acc.rev(r: Wr.Dec<Nat>) -> Wr.Dec<V.Acc>:
  match r:
    case Wr.Got{rev, s}:
      r_acc.slots(rev, r_slots(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_acc(s: String) -> Wr.Dec<V.Acc>:
  r_acc.rev(Wr.get_nat(s))

def r_actor(r: Wr.Dec<Nat>) -> Wr.Dec<V.Actor>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{V.Owner{}, s}
        case 1n:
          Wr.Got{V.Worker{}, s}
        case 2n:
          Wr.Got{V.Verifier{}, s}
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_evidence.code(r: Wr.Dec<Nat>) -> Wr.Dec<V.Evidence>:
  match r:
    case Wr.Got{code, s}:
      Wr.Got{V.Exited{code}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_evidence(r: Wr.Dec<Nat>) -> Wr.Dec<V.Evidence>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          r_evidence.code(Wr.get_nat(s))
        case 1n:
          Wr.Got{V.NoStatus{}, s}
        case 2n:
          Wr.Got{V.TimedOut{}, s}
        case 3n:
          Wr.Got{V.SpawnFailed{}, s}
        case 4n:
          Wr.Got{V.Cancelled{}, s}
        case 5n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_answer(r: Wr.Dec<Nat>) -> Wr.Dec<V.Answer>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{V.Yes{}, s}
        case 1n:
          Wr.Got{V.No{}, s}
        case 2n:
          Wr.Got{V.Unreadable{}, s}
        case 3n:
          Wr.Got{V.Unavailable{}, s}
        case 4n:
          Wr.Got{V.Stopped{}, s}
        case 5n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_op.assign(r: Wr.Dec<Nat>) -> Wr.Dec<V.Op>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{V.Assign{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_op.at(of: Nat, i: Nat, v: V.Verdict, r: Wr.Dec<Nat>) -> Wr.Dec<V.Op>:
  match r:
    case Wr.Got{at, s}:
      Wr.Got{V.Record{of, i, v, at}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_op.verdict(of: Nat, i: Nat, r: Wr.Dec<V.Verdict>) -> Wr.Dec<V.Op>:
  match r:
    case Wr.Got{v, s}:
      r_op.at(of, i, v, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_op.index(of: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<V.Op>:
  match r:
    case Wr.Got{i, s}:
      r_op.verdict(of, i, r_verdict(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_op.rev(r: Wr.Dec<Nat>) -> Wr.Dec<V.Op>:
  match r:
    case Wr.Got{of, s}:
      r_op.index(of, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_op(r: Wr.Dec<Nat>) -> Wr.Dec<V.Op>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          r_op.assign(Wr.get_nat(s))
        case 1n:
          Wr.Got{V.Claim{}, s}
        case 2n:
          r_op.rev(Wr.get_nat(s))
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.act_a(who: V.Actor, op: V.Op, r: Wr.Dec<V.Acc>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{FV.QAct{who, op, a}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.act_op(who: V.Actor, r: Wr.Dec<V.Op>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{op, s}:
      r_req.act_a(who, op, r_acc(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.act(r: Wr.Dec<V.Actor>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{who, s}:
      r_req.act_op(who, r_op(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.advance_a(now: Nat, cap: Nat, r: Wr.Dec<V.Acc>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{FV.QAdvance{now, cap, a}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.advance_cap(now: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{cap, s}:
      r_req.advance_a(now, cap, r_acc(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.advance(r: Wr.Dec<Nat>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{now, s}:
      r_req.advance_cap(now, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.label_s(now: Nat, r: Wr.Dec<List<&2, V.Slot>>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{slots, s}:
      Wr.Got{FV.QLabel{now, slots}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.label(r: Wr.Dec<Nat>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{now, s}:
      r_req.label_s(now, r_slots(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit_s(base: Nat, now: Nat, r: Wr.Dec<List<&2, V.Slot>>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{slots, s}:
      Wr.Got{FV.QExit{base, now, slots}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit_now(base: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{now, s}:
      r_req.exit_s(base, now, r_slots(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit(r: Wr.Dec<Nat>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{base, s}:
      r_req.exit_now(base, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.command_ev(expect: Nat, intact: Bool, r: Wr.Dec<V.Evidence>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{ev, s}:
      Wr.Got{FV.QCommand{expect, intact, ev}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.command_intact(expect: Nat, r: Wr.Dec<Bool>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{intact, s}:
      r_req.command_ev(expect, intact, r_evidence(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.command(r: Wr.Dec<Nat>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{expect, s}:
      r_req.command_intact(expect, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.until(r: Wr.Dec<V.Evidence>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{ev, s}:
      Wr.Got{FV.QUntil{ev}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.judge(r: Wr.Dec<V.Answer>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{ans, s}:
      Wr.Got{FV.QJudge{ans}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.claims_e(held: Bool, checked: Bool, goal: Bool, claimed: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{ended, s}:
      Wr.Got{FV.QClaims{held, checked, goal, claimed, ended}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.claims_c(held: Bool, checked: Bool, goal: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{claimed, s}:
      r_req.claims_e(held, checked, goal, claimed, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.claims_g(held: Bool, checked: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{goal, s}:
      r_req.claims_c(held, checked, goal, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.claims_k(held: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{checked, s}:
      r_req.claims_g(held, checked, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.claims(r: Wr.Dec<Bool>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{held, s}:
      r_req.claims_k(held, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req(r: Wr.Dec<Nat>) -> Wr.Dec<FV.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          r_req.act(r_actor(Wr.get_nat(s)))
        case 1n:
          r_req.advance(Wr.get_nat(s))
        case 2n:
          r_req.label(Wr.get_nat(s))
        case 3n:
          r_req.exit(Wr.get_nat(s))
        case 4n:
          r_req.command(Wr.get_nat(s))
        case 5n:
          r_req.until(r_evidence(Wr.get_nat(s)))
        case 6n:
          r_req.judge(r_answer(Wr.get_nat(s)))
        case 7n:
          r_req.claims(Wr.get_bool(s))
        case 8n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_whole.end(b: Bool, q: FV.Req) -> Maybe<&2, FV.Req>:
  match b:
    case True{}:
      Some{q}
    case False{}:
      None{}

def r_whole(r: Wr.Dec<FV.Req>) -> Maybe<&2, FV.Req>:
  match r:
    case Wr.Got{q, s}:
      r_whole.end(Wr.end(s), q)
    case Wr.Bad{}:
      None{}

# the request s spells whole, with nothing after it
def read(s: String) -> Maybe<&2, FV.Req>:
  r_whole(r_req(Wr.get_nat(s)))

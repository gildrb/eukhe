# eukhe: lemmas of the entry proofs of area verify: the entry's decoder
# reads every input as the laws' reader does (vr.verdict to vr.req: stage
# by stage; the slots by their item loop, vr.list_go), and what the entry
# answers on what that reader read: its answer to the request read whole
# (vr.got_some), its error form where no request is read whole
# (vr.got_none)

import Base
import ../../../bend/verify.bend as V
import ../../../bend/ffi_verify.bend as FV
import ../../../bend/wire.bend as Wr
import ../../../spec/verified/verify_wire.bend as SW

# Verdicts and slots
# ------------------

def vr.verdict(d: Wr.Dec<Nat>) -> {FV.get_verdict(d) == SW.r_verdict(d) : Wr.Dec<V.Verdict>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n+u:
          {==}
    case Wr.Bad{}:
      {==}

def vr.slot_at(v: V.Verdict, d: Wr.Dec<Nat>) -> {FV.get_slot.at(v, d) == SW.r_slot.at(v, d) : Wr.Dec<V.Slot>}:
  match d:
    case Wr.Got{at, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.slot_verdict(d: Wr.Dec<V.Verdict>) -> {FV.get_slot.verdict(d) == SW.r_slot.verdict(d) : Wr.Dec<V.Slot>}:
  match d:
    case Wr.Got{v, s}:
      vr.slot_at(v, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def vr.slot_tag(d: Wr.Dec<Nat>) -> {FV.get_slot.tag(d) == SW.r_slot.tag(d) : Wr.Dec<V.Slot>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          {==}
        case 1n:
          %vr.verdict(Wr.get_nat(s)) : {FV.get_slot.verdict(FV.get_verdict(Wr.get_nat(s))) == SW.r_slot.verdict(_) : Wr.Dec<V.Slot>}
          vr.slot_verdict(FV.get_verdict(Wr.get_nat(s)))
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def vr.slot(s: String) -> {FV.get_slot(s) == SW.r_slot(s) : Wr.Dec<V.Slot>}:
  vr.slot_tag(Wr.get_nat(s))

# the item loops read the same slots
def vr.list_go(n: Nat, cur: Wr.Dec<V.Slot>) -> {Wr.get_list.go(~V.Slot, ~FV.get_slot, n, cur) == Wr.get_list.go(~V.Slot, ~SW.r_slot, n, cur) : Wr.Dec<List<&2, V.Slot>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %vr.slot(s) : {Wr.get_list.cons(V.Slot, x, Wr.get_list.go(~V.Slot, ~FV.get_slot, m, FV.get_slot(s))) == Wr.get_list.cons(V.Slot, x, Wr.get_list.go(~V.Slot, ~SW.r_slot, m, _)) : Wr.Dec<List<&2, V.Slot>>}
          %vr.list_go(m, FV.get_slot(s)) : {Wr.get_list.cons(V.Slot, x, Wr.get_list.go(~V.Slot, ~FV.get_slot, m, FV.get_slot(s))) == Wr.get_list.cons(V.Slot, x, _) : Wr.Dec<List<&2, V.Slot>>}
          {==}
        case Wr.Bad{}:
          {==}

def vr.list_start(d: Wr.Dec<Nat>) -> {Wr.get_list.start(~V.Slot, ~FV.get_slot, d) == Wr.get_list.start(~V.Slot, ~SW.r_slot, d) : Wr.Dec<List<&2, V.Slot>>}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %vr.slot(s) : {Wr.get_list.go(~V.Slot, ~FV.get_slot, m, FV.get_slot(s)) == Wr.get_list.go(~V.Slot, ~SW.r_slot, m, _) : Wr.Dec<List<&2, V.Slot>>}
          vr.list_go(m, FV.get_slot(s))
    case Wr.Bad{}:
      {==}

def vr.slots(s: String) -> {FV.get_slots(s) == SW.r_slots(s) : Wr.Dec<List<&2, V.Slot>>}:
  vr.list_start(Wr.get_nat(s))

# Acceptances
# -----------

def vr.acc_tries(rev: Nat, slots: List<&2, V.Slot>, claimed: Bool, d: Wr.Dec<Nat>) -> {FV.get_acc.tries(rev, slots, claimed, d) == SW.r_acc.tries(rev, slots, claimed, d) : Wr.Dec<V.Acc>}:
  match d:
    case Wr.Got{tries, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.acc_claimed(rev: Nat, slots: List<&2, V.Slot>, d: Wr.Dec<Bool>) -> {FV.get_acc.claimed(rev, slots, d) == SW.r_acc.claimed(rev, slots, d) : Wr.Dec<V.Acc>}:
  match d:
    case Wr.Got{claimed, s}:
      vr.acc_tries(rev, slots, claimed, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def vr.acc_slots(rev: Nat, d: Wr.Dec<List<&2, V.Slot>>) -> {FV.get_acc.slots(rev, d) == SW.r_acc.slots(rev, d) : Wr.Dec<V.Acc>}:
  match d:
    case Wr.Got{slots, s}:
      vr.acc_claimed(rev, slots, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def vr.acc_rev(d: Wr.Dec<Nat>) -> {FV.get_acc.rev(d) == SW.r_acc.rev(d) : Wr.Dec<V.Acc>}:
  match d:
    case Wr.Got{+rev, +s}:
      %vr.slots(s) : {FV.get_acc.slots(rev, FV.get_slots(s)) == SW.r_acc.slots(rev, _) : Wr.Dec<V.Acc>}
      vr.acc_slots(rev, FV.get_slots(s))
    case Wr.Bad{}:
      {==}

def vr.acc(s: String) -> {FV.get_acc(s) == SW.r_acc(s) : Wr.Dec<V.Acc>}:
  vr.acc_rev(Wr.get_nat(s))

# Actors, evidence, answers
# -------------------------

def vr.actor(d: Wr.Dec<Nat>) -> {FV.get_actor(d) == SW.r_actor(d) : Wr.Dec<V.Actor>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def vr.evidence_code(d: Wr.Dec<Nat>) -> {FV.get_evidence.code(d) == SW.r_evidence.code(d) : Wr.Dec<V.Evidence>}:
  match d:
    case Wr.Got{code, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.evidence(d: Wr.Dec<Nat>) -> {FV.get_evidence(d) == SW.r_evidence(d) : Wr.Dec<V.Evidence>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          vr.evidence_code(Wr.get_nat(s))
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n+u:
          {==}
    case Wr.Bad{}:
      {==}

def vr.answer(d: Wr.Dec<Nat>) -> {FV.get_answer(d) == SW.r_answer(d) : Wr.Dec<V.Answer>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n+u:
          {==}
    case Wr.Bad{}:
      {==}

# Acts
# ----

def vr.op_assign(d: Wr.Dec<Nat>) -> {FV.get_op.assign(d) == SW.r_op.assign(d) : Wr.Dec<V.Op>}:
  match d:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.op_at(rv: Nat, i: Nat, v: V.Verdict, d: Wr.Dec<Nat>) -> {FV.get_op.at(rv, i, v, d) == SW.r_op.at(rv, i, v, d) : Wr.Dec<V.Op>}:
  match d:
    case Wr.Got{at, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.op_verdict(rv: Nat, i: Nat, d: Wr.Dec<V.Verdict>) -> {FV.get_op.verdict(rv, i, d) == SW.r_op.verdict(rv, i, d) : Wr.Dec<V.Op>}:
  match d:
    case Wr.Got{v, s}:
      vr.op_at(rv, i, v, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def vr.op_index(rv: Nat, d: Wr.Dec<Nat>) -> {FV.get_op.index(rv, d) == SW.r_op.index(rv, d) : Wr.Dec<V.Op>}:
  match d:
    case Wr.Got{+i, +s}:
      %vr.verdict(Wr.get_nat(s)) : {FV.get_op.verdict(rv, i, FV.get_verdict(Wr.get_nat(s))) == SW.r_op.verdict(rv, i, _) : Wr.Dec<V.Op>}
      vr.op_verdict(rv, i, FV.get_verdict(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def vr.op_rev(d: Wr.Dec<Nat>) -> {FV.get_op.rev(d) == SW.r_op.rev(d) : Wr.Dec<V.Op>}:
  match d:
    case Wr.Got{rv, s}:
      vr.op_index(rv, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def vr.op(d: Wr.Dec<Nat>) -> {FV.get_op(d) == SW.r_op(d) : Wr.Dec<V.Op>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          vr.op_assign(Wr.get_nat(s))
        case 1n:
          {==}
        case 2n:
          vr.op_rev(Wr.get_nat(s))
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

# Requests
# --------

def vr.act_a(who: V.Actor, op: V.Op, d: Wr.Dec<V.Acc>) -> {FV.get_req.act_a(who, op, d) == SW.r_req.act_a(who, op, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.act_op(who: V.Actor, d: Wr.Dec<V.Op>) -> {FV.get_req.act_op(who, d) == SW.r_req.act_op(who, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{+op, +s}:
      %vr.acc(s) : {FV.get_req.act_a(who, op, FV.get_acc(s)) == SW.r_req.act_a(who, op, _) : Wr.Dec<FV.Req>}
      vr.act_a(who, op, FV.get_acc(s))
    case Wr.Bad{}:
      {==}

def vr.act(d: Wr.Dec<V.Actor>) -> {FV.get_req.act(d) == SW.r_req.act(d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{+who, +s}:
      %vr.op(Wr.get_nat(s)) : {FV.get_req.act_op(who, FV.get_op(Wr.get_nat(s))) == SW.r_req.act_op(who, _) : Wr.Dec<FV.Req>}
      vr.act_op(who, FV.get_op(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def vr.advance_a(now: Nat, cap: Nat, d: Wr.Dec<V.Acc>) -> {FV.get_req.advance_a(now, cap, d) == SW.r_req.advance_a(now, cap, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.advance_cap(now: Nat, d: Wr.Dec<Nat>) -> {FV.get_req.advance_cap(now, d) == SW.r_req.advance_cap(now, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{+cap, +s}:
      %vr.acc(s) : {FV.get_req.advance_a(now, cap, FV.get_acc(s)) == SW.r_req.advance_a(now, cap, _) : Wr.Dec<FV.Req>}
      vr.advance_a(now, cap, FV.get_acc(s))
    case Wr.Bad{}:
      {==}

def vr.advance(d: Wr.Dec<Nat>) -> {FV.get_req.advance(d) == SW.r_req.advance(d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{now, s}:
      vr.advance_cap(now, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def vr.label_s(now: Nat, d: Wr.Dec<List<&2, V.Slot>>) -> {FV.get_req.label_s(now, d) == SW.r_req.label_s(now, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{slots, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.label(d: Wr.Dec<Nat>) -> {FV.get_req.label(d) == SW.r_req.label(d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{+now, +s}:
      %vr.slots(s) : {FV.get_req.label_s(now, FV.get_slots(s)) == SW.r_req.label_s(now, _) : Wr.Dec<FV.Req>}
      vr.label_s(now, FV.get_slots(s))
    case Wr.Bad{}:
      {==}

def vr.exit_s(base: Nat, now: Nat, d: Wr.Dec<List<&2, V.Slot>>) -> {FV.get_req.exit_s(base, now, d) == SW.r_req.exit_s(base, now, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{slots, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.exit_now(base: Nat, d: Wr.Dec<Nat>) -> {FV.get_req.exit_now(base, d) == SW.r_req.exit_now(base, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{+now, +s}:
      %vr.slots(s) : {FV.get_req.exit_s(base, now, FV.get_slots(s)) == SW.r_req.exit_s(base, now, _) : Wr.Dec<FV.Req>}
      vr.exit_s(base, now, FV.get_slots(s))
    case Wr.Bad{}:
      {==}

def vr.exit(d: Wr.Dec<Nat>) -> {FV.get_req.exit(d) == SW.r_req.exit(d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{base, s}:
      vr.exit_now(base, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def vr.command_ev(expect: Nat, intact: Bool, d: Wr.Dec<V.Evidence>) -> {FV.get_req.command_ev(expect, intact, d) == SW.r_req.command_ev(expect, intact, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{ev, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.command_intact(expect: Nat, d: Wr.Dec<Bool>) -> {FV.get_req.command_intact(expect, d) == SW.r_req.command_intact(expect, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{+intact, +s}:
      %vr.evidence(Wr.get_nat(s)) : {FV.get_req.command_ev(expect, intact, FV.get_evidence(Wr.get_nat(s))) == SW.r_req.command_ev(expect, intact, _) : Wr.Dec<FV.Req>}
      vr.command_ev(expect, intact, FV.get_evidence(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def vr.command(d: Wr.Dec<Nat>) -> {FV.get_req.command(d) == SW.r_req.command(d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{expect, s}:
      vr.command_intact(expect, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def vr.until(d: Wr.Dec<V.Evidence>) -> {FV.get_req.until(d) == SW.r_req.until(d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{ev, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.judge(d: Wr.Dec<V.Answer>) -> {FV.get_req.judge(d) == SW.r_req.judge(d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{ans, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.claims_e(held: Bool, checked: Bool, goal: Bool, claimed: Bool, d: Wr.Dec<Bool>) -> {FV.get_req.claims_e(held, checked, goal, claimed, d) == SW.r_req.claims_e(held, checked, goal, claimed, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{ended, s}:
      {==}
    case Wr.Bad{}:
      {==}

def vr.claims_c(held: Bool, checked: Bool, goal: Bool, d: Wr.Dec<Bool>) -> {FV.get_req.claims_c(held, checked, goal, d) == SW.r_req.claims_c(held, checked, goal, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{claimed, s}:
      vr.claims_e(held, checked, goal, claimed, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def vr.claims_g(held: Bool, checked: Bool, d: Wr.Dec<Bool>) -> {FV.get_req.claims_g(held, checked, d) == SW.r_req.claims_g(held, checked, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{goal, s}:
      vr.claims_c(held, checked, goal, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def vr.claims_k(held: Bool, d: Wr.Dec<Bool>) -> {FV.get_req.claims_k(held, d) == SW.r_req.claims_k(held, d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{checked, s}:
      vr.claims_g(held, checked, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def vr.claims(d: Wr.Dec<Bool>) -> {FV.get_req.claims(d) == SW.r_req.claims(d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{held, s}:
      vr.claims_k(held, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

# the entry's decoder is the laws' reader
def vr.req(d: Wr.Dec<Nat>) -> {FV.get_req(d) == SW.r_req(d) : Wr.Dec<FV.Req>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          %vr.actor(Wr.get_nat(s)) : {FV.get_req.act(FV.get_actor(Wr.get_nat(s))) == SW.r_req.act(_) : Wr.Dec<FV.Req>}
          vr.act(FV.get_actor(Wr.get_nat(s)))
        case 1n:
          vr.advance(Wr.get_nat(s))
        case 2n:
          vr.label(Wr.get_nat(s))
        case 3n:
          vr.exit(Wr.get_nat(s))
        case 4n:
          vr.command(Wr.get_nat(s))
        case 5n:
          %vr.evidence(Wr.get_nat(s)) : {FV.get_req.until(FV.get_evidence(Wr.get_nat(s))) == SW.r_req.until(_) : Wr.Dec<FV.Req>}
          vr.until(FV.get_evidence(Wr.get_nat(s)))
        case 6n:
          %vr.answer(Wr.get_nat(s)) : {FV.get_req.judge(FV.get_answer(Wr.get_nat(s))) == SW.r_req.judge(_) : Wr.Dec<FV.Req>}
          vr.judge(FV.get_answer(Wr.get_nat(s)))
        case 7n:
          vr.claims(Wr.get_bool(s))
        case 8n+u:
          {==}
    case Wr.Bad{}:
      {==}

# The entry on what the reader read
# ---------------------------------

def vr.MS(m: Maybe<&2, FV.Req>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def vr.none_some(-q: FV.Req, -G: Type, e: {None{} == Some{q} : Maybe<&2, FV.Req>}) -> G:
  %e : vr.MS(_, G)
  Unit{}

def vr.MN(m: Maybe<&2, FV.Req>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def vr.some_none(-q: FV.Req, -G: Type, e: {Some{q} == None{} : Maybe<&2, FV.Req>}) -> G:
  %e : vr.MN(_, G)
  Unit{}

def vr.val(d: FV.Req, m: Maybe<&2, FV.Req>) -> FV.Req:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is one to one
def vr.some(+p: FV.Req, +q: FV.Req, e: {Some{p} == Some{q} : Maybe<&2, FV.Req>}) -> {q == p : FV.Req}:
  Equal.sym(FV.Req, p, q, Equal.cong(Maybe<&2, FV.Req>, FV.Req, m => vr.val(p, m), Some{p}, Some{q}, e))

def vr.end_some(b: Bool, +q: FV.Req, +p: FV.Req, got: {SW.r_whole.end(b, p) == Some{q} : Maybe<&2, FV.Req>}) -> {FV.ffi.done(p, b) == FV.answer(q) : String}:
  match b:
    case True{}:
      %vr.some(p, q, got) : {FV.answer(_) == FV.answer(q) : String}
      {==}
    case False{}:
      vr.none_some(q, {FV.ffi.done(p, False{}) == FV.answer(q) : String}, got)

# where the reader finds the whole request q, the entry answers q
def vr.got_some(r: Wr.Dec<FV.Req>, +q: FV.Req, got: {SW.r_whole(r) == Some{q} : Maybe<&2, FV.Req>}) -> {FV.ffi.got(r) == FV.answer(q) : String}:
  match r:
    case Wr.Got{p, +s}:
      vr.end_some(Wr.end(s), q, p, got)
    case Wr.Bad{}:
      vr.none_some(q, {Wr.err("verify: malformed request") == FV.answer(q) : String}, got)

def vr.end_none(b: Bool, -q: FV.Req, no: {SW.r_whole.end(b, q) == None{} : Maybe<&2, FV.Req>}) -> {FV.ffi.done(q, b) == Wr.err("verify: malformed request") : String}:
  match b:
    case True{}:
      vr.some_none(q, {FV.answer(q) == Wr.err("verify: malformed request") : String}, no)
    case False{}:
      {==}

# where the reader finds no whole request, the entry answers its error form
def vr.got_none(r: Wr.Dec<FV.Req>, no: {SW.r_whole(r) == None{} : Maybe<&2, FV.Req>}) -> {FV.ffi.got(r) == Wr.err("verify: malformed request") : String}:
  match r:
    case Wr.Got{q, +s}:
      vr.end_none(Wr.end(s), q, no)
    case Wr.Bad{}:
      {==}

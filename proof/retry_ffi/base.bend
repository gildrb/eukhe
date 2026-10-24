# eukhe: lemmas the proofs of area retry_ffi share: the laws' spelling is
# the entry's encoding, and the laws' reader the entry's decoder

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_ffi.bend as RetryFfi

# Spelling
# --------

def rf.mnat(m: Maybe<&2, Nat>, rest: String) -> {RetryFfi.spell_mnat(m, rest) == Fr.put_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def rf.cause(k: R.Cause) -> {RetryFfi.cause_num(k) == Fr.cause.tag(k) : Nat}:
  match k:
    case R.Refusal{}:
      {==}
    case R.Safety{}:
      {==}
    case R.PaymentRequired{}:
      {==}
    case R.Overloaded{}:
      {==}
    case R.RateLimit{}:
      {==}
    case R.ServerError{}:
      {==}
    case R.Auth{}:
      {==}
    case R.Permission{}:
      {==}
    case R.InvalidRequest{}:
      {==}
    case R.MalformedResponse{}:
      {==}
    case R.StreamDrop{}:
      {==}
    case R.StreamStalled{}:
      {==}
    case R.StreamRepeating{}:
      {==}
    case R.Unknown{}:
      {==}

def rf.mcause(m: Maybe<&2, R.Cause>, rest: String) -> {RetryFfi.spell_mcause(m, rest) == Fr.put_mcause(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+k}:
      %Equal.sym(Nat, RetryFfi.cause_num(k), Fr.cause.tag(k), rf.cause(k)) : {Wr.put_nat(1n, Wr.put_nat(_, rest)) == Fr.put_mcause(Some{k}, rest) : String}
      {==}

def rf.tried(t: R.Tried, rest: String) -> {RetryFfi.spell_tried(t, rest) == Fr.put_tried(t, rest) : String}:
  match t:
    case R.Tried{at, w}:
      Equal.cong(String, String, x => Wr.put_nat(at, x), RetryFfi.spell_mnat(w, rest), Fr.put_mnat(w, rest), rf.mnat(w, rest))

def rf.step(x: R.Tried, p: Nat & String) -> {Wr.put_list.step(~R.Tried, ~RetryFfi.spell_tried, x, p) == Wr.put_list.step(~R.Tried, ~Fr.put_tried, x, p) : Nat & String}:
  (n, s) = p
  Equal.cong(String, Nat & String, y => (1n+n, y), RetryFfi.spell_tried(x, s), Fr.put_tried(x, s), rf.tried(x, s))

def rf.put_go(ts: List<&2, R.Tried>, +rest: String) -> {Wr.put_list.go(~R.Tried, ~RetryFfi.spell_tried, ts, rest) == Wr.put_list.go(~R.Tried, ~Fr.put_tried, ts, rest) : Nat & String}:
  match ts:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~R.Tried, ~RetryFfi.spell_tried, t, rest), Wr.put_list.go(~R.Tried, ~Fr.put_tried, t, rest), rf.put_go(t, rest)) : {Wr.put_list.step(~R.Tried, ~RetryFfi.spell_tried, x, _) == Wr.put_list.step(~R.Tried, ~Fr.put_tried, x, Wr.put_list.go(~R.Tried, ~Fr.put_tried, t, rest)) : Nat & String}
      rf.step(x, Wr.put_list.go(~R.Tried, ~Fr.put_tried, t, rest))

def rf.put_list(+ts: List<&2, R.Tried>, +rest: String) -> {Wr.put_list(~R.Tried, ~RetryFfi.spell_tried, ts, rest) == Wr.put_list(~R.Tried, ~Fr.put_tried, ts, rest) : String}:
  Equal.cong(Nat & String, String, y => Wr.put_list.fin(y), Wr.put_list.go(~R.Tried, ~RetryFfi.spell_tried, ts, rest), Wr.put_list.go(~R.Tried, ~Fr.put_tried, ts, rest), rf.put_go(ts, rest))

# the laws spell every request as the entry's encoder writes it
def rf.req(q: Fr.Req) -> {RetryFfi.spell_req(q) == Fr.put_req(q, "") : String}:
  match q:
    case Fr.QClassify{f}:
      match f:
        case R.Facts{parked, limit, +status, +kind, +text}:
          %Equal.sym(String, RetryFfi.spell_mcause(kind, Wr.put_bool(text, "")), Fr.put_mcause(kind, Wr.put_bool(text, "")), rf.mcause(kind, Wr.put_bool(text, ""))) : {Wr.put_nat(0n, Wr.put_bool(parked, Wr.put_bool(limit, RetryFfi.spell_mnat(status, _)))) == Fr.put_req(Fr.QClassify{R.Facts{parked, limit, status, kind, text}}, "") : String}
          %Equal.sym(String, RetryFfi.spell_mnat(status, Fr.put_mcause(kind, Wr.put_bool(text, ""))), Fr.put_mnat(status, Fr.put_mcause(kind, Wr.put_bool(text, ""))), rf.mnat(status, Fr.put_mcause(kind, Wr.put_bool(text, "")))) : {Wr.put_nat(0n, Wr.put_bool(parked, Wr.put_bool(limit, _))) == Fr.put_req(Fr.QClassify{R.Facts{parked, limit, status, kind, text}}, "") : String}
          {==}
    case Fr.QWait{base, attempt, cap, draw, server}:
      Equal.cong(String, String, x => Wr.put_nat(1n, Wr.put_nat(base, Wr.put_nat(attempt, Wr.put_nat(cap, Wr.put_nat(draw, x))))), RetryFfi.spell_mnat(server, ""), Fr.put_mnat(server, ""), rf.mnat(server, ""))
    case Fr.QFailover{len, tried, p}:
      match p:
        case R.Policy{switches, base, max}:
          Equal.cong(String, String, x => Wr.put_nat(2n, Wr.put_nat(len, x)), Wr.put_list(~R.Tried, ~RetryFfi.spell_tried, tried, Wr.put_nat(switches, Wr.put_nat(base, Wr.put_nat(max, "")))), Wr.put_list(~R.Tried, ~Fr.put_tried, tried, Wr.put_nat(switches, Wr.put_nat(base, Wr.put_nat(max, "")))), rf.put_list(tried, Wr.put_nat(switches, Wr.put_nat(base, Wr.put_nat(max, "")))))
    case Fr.QStall{idle}:
      {==}

def rf.delay(d: R.Delay) -> {Fr.put_delay(d, "") == RetryFfi.spell_delay(d) : String}:
  match d:
    case R.After{ms}:
      {==}
    case R.Refused{server, cap}:
      {==}

def rf.switch(m: Maybe<&2, R.Switch>) -> {Fr.put_switch(m, "") == RetryFfi.spell_switch(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{sw}:
      match sw:
        case R.Switch{to, delay}:
          {==}

# The reader
# ----------

def rf.mn_some(r: Wr.Dec<Nat>) -> {RetryFfi.read_mnat.some(r) == Fr.get_mnat.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{n, u}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.rd_mnat_tag(r: Wr.Dec<Nat>) -> {RetryFfi.read_mnat.tag(r) == Fr.get_mnat.tag(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          rf.mn_some(Wr.get_nat(s))
        case 2n+k:
          {==}
    case Wr.Bad{}:
      {==}

def rf.rd_mnat(s: String) -> {RetryFfi.read_mnat(s) == Fr.get_mnat(s) : Wr.Dec<Maybe<&2, Nat>>}:
  rf.rd_mnat_tag(Wr.get_nat(s))

def rf.cause_of(t: Nat) -> {RetryFfi.cause_of(t) == Fr.cause.of(t) : Maybe<&2, R.Cause>}:
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
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n+u:
      {==}

def rf.known(m: Maybe<&2, R.Cause>, s: String) -> {RetryFfi.read_mcause.known(m, s) == Fr.get_mcause.known(m, s) : Wr.Dec<Maybe<&2, R.Cause>>}:
  match m:
    case Some{k}:
      {==}
    case None{}:
      {==}

def rf.mc_some(r: Wr.Dec<Nat>) -> {RetryFfi.read_mcause.some(r) == Fr.get_mcause.some(r) : Wr.Dec<Maybe<&2, R.Cause>>}:
  match r:
    case Wr.Got{+t, +s}:
      %Equal.sym(Maybe<&2, R.Cause>, RetryFfi.cause_of(t), Fr.cause.of(t), rf.cause_of(t)) : {RetryFfi.read_mcause.known(_, s) == Fr.get_mcause.known(Fr.cause.of(t), s) : Wr.Dec<Maybe<&2, R.Cause>>}
      rf.known(Fr.cause.of(t), s)
    case Wr.Bad{}:
      {==}

def rf.mc_tag(r: Wr.Dec<Nat>) -> {RetryFfi.read_mcause.tag(r) == Fr.get_mcause.tag(r) : Wr.Dec<Maybe<&2, R.Cause>>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          rf.mc_some(Wr.get_nat(s))
        case 2n+k:
          {==}
    case Wr.Bad{}:
      {==}

def rf.rd_mcause(s: String) -> {RetryFfi.read_mcause(s) == Fr.get_mcause(s) : Wr.Dec<Maybe<&2, R.Cause>>}:
  rf.mc_tag(Wr.get_nat(s))

# the laws' Facts reader against the entry's, stage by stage: the entry
# reads Facts and wraps them in QClassify
def rf.f_text(parked: Bool, limit: Bool, status: Maybe<&2, Nat>, kind: Maybe<&2, R.Cause>, r: Wr.Dec<Bool>) -> {RetryFfi.read_facts.text(parked, limit, status, kind, r) == Fr.get_classify(Fr.get_facts.text(parked, limit, status, kind, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{text, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.f_kind(parked: Bool, limit: Bool, status: Maybe<&2, Nat>, r: Wr.Dec<Maybe<&2, R.Cause>>) -> {RetryFfi.read_facts.kind(parked, limit, status, r) == Fr.get_classify(Fr.get_facts.kind(parked, limit, status, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{kind, s}:
      rf.f_text(parked, limit, status, kind, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def rf.f_status(parked: Bool, limit: Bool, r: Wr.Dec<Maybe<&2, Nat>>) -> {RetryFfi.read_facts.status(parked, limit, r) == Fr.get_classify(Fr.get_facts.status(parked, limit, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{status, +s}:
      %Equal.sym(Wr.Dec<Maybe<&2, R.Cause>>, RetryFfi.read_mcause(s), Fr.get_mcause(s), rf.rd_mcause(s)) : {RetryFfi.read_facts.kind(parked, limit, status, _) == Fr.get_classify(Fr.get_facts.kind(parked, limit, status, Fr.get_mcause(s))) : Wr.Dec<Fr.Req>}
      rf.f_kind(parked, limit, status, Fr.get_mcause(s))
    case Wr.Bad{}:
      {==}

def rf.f_limit(parked: Bool, r: Wr.Dec<Bool>) -> {RetryFfi.read_facts.limit(parked, r) == Fr.get_classify(Fr.get_facts.limit(parked, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{limit, +s}:
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, RetryFfi.read_mnat(s), Fr.get_mnat(s), rf.rd_mnat(s)) : {RetryFfi.read_facts.status(parked, limit, _) == Fr.get_classify(Fr.get_facts.status(parked, limit, Fr.get_mnat(s))) : Wr.Dec<Fr.Req>}
      rf.f_status(parked, limit, Fr.get_mnat(s))
    case Wr.Bad{}:
      {==}

def rf.facts(r: Wr.Dec<Bool>) -> {RetryFfi.read_facts(r) == Fr.get_classify(Fr.get_facts.parked(r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{parked, s}:
      rf.f_limit(parked, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def rf.w_server(base: Nat, attempt: Nat, cap: Nat, draw: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> {RetryFfi.read_wait.server(base, attempt, cap, draw, r) == Fr.get_wait.server(base, attempt, cap, draw, r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{server, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.w_draw(base: Nat, attempt: Nat, cap: Nat, r: Wr.Dec<Nat>) -> {RetryFfi.read_wait.draw(base, attempt, cap, r) == Fr.get_wait.draw(base, attempt, cap, r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{draw, +s}:
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, RetryFfi.read_mnat(s), Fr.get_mnat(s), rf.rd_mnat(s)) : {RetryFfi.read_wait.server(base, attempt, cap, draw, _) == Fr.get_wait.server(base, attempt, cap, draw, Fr.get_mnat(s)) : Wr.Dec<Fr.Req>}
      rf.w_server(base, attempt, cap, draw, Fr.get_mnat(s))
    case Wr.Bad{}:
      {==}

def rf.w_cap(base: Nat, attempt: Nat, r: Wr.Dec<Nat>) -> {RetryFfi.read_wait.cap(base, attempt, r) == Fr.get_wait.cap(base, attempt, r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{cap, s}:
      rf.w_draw(base, attempt, cap, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.w_attempt(base: Nat, r: Wr.Dec<Nat>) -> {RetryFfi.read_wait.attempt(base, r) == Fr.get_wait.attempt(base, r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{attempt, s}:
      rf.w_cap(base, attempt, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.wait(r: Wr.Dec<Nat>) -> {RetryFfi.read_wait(r) == Fr.get_wait(r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{base, s}:
      rf.w_attempt(base, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.t_wait(at: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> {RetryFfi.read_tried.wait(at, r) == Fr.get_tried.wait(at, r) : Wr.Dec<R.Tried>}:
  match r:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.t_at(r: Wr.Dec<Nat>) -> {RetryFfi.read_tried.at(r) == Fr.get_tried.at(r) : Wr.Dec<R.Tried>}:
  match r:
    case Wr.Got{at, +s}:
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, RetryFfi.read_mnat(s), Fr.get_mnat(s), rf.rd_mnat(s)) : {RetryFfi.read_tried.wait(at, _) == Fr.get_tried.wait(at, Fr.get_mnat(s)) : Wr.Dec<R.Tried>}
      rf.t_wait(at, Fr.get_mnat(s))
    case Wr.Bad{}:
      {==}

def rf.rd_tried(s: String) -> {RetryFfi.read_tried(s) == Fr.get_tried(s) : Wr.Dec<R.Tried>}:
  rf.t_at(Wr.get_nat(s))

def rf.list_go(n: Nat, cur: Wr.Dec<R.Tried>) -> {Wr.get_list.go(~R.Tried, ~RetryFfi.read_tried, n, cur) == Wr.get_list.go(~R.Tried, ~Fr.get_tried, n, cur) : Wr.Dec<List<&2, R.Tried>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{x, +s}:
          %Equal.sym(Wr.Dec<R.Tried>, RetryFfi.read_tried(s), Fr.get_tried(s), rf.rd_tried(s)) : {Wr.get_list.cons(R.Tried, x, Wr.get_list.go(~R.Tried, ~RetryFfi.read_tried, m, _)) == Wr.get_list.cons(R.Tried, x, Wr.get_list.go(~R.Tried, ~Fr.get_tried, m, Fr.get_tried(s))) : Wr.Dec<List<&2, R.Tried>>}
          Equal.cong(Wr.Dec<List<&2, R.Tried>>, Wr.Dec<List<&2, R.Tried>>, y => Wr.get_list.cons(R.Tried, x, y), Wr.get_list.go(~R.Tried, ~RetryFfi.read_tried, m, Fr.get_tried(s)), Wr.get_list.go(~R.Tried, ~Fr.get_tried, m, Fr.get_tried(s)), rf.list_go(m, Fr.get_tried(s)))
        case Wr.Bad{}:
          {==}

def rf.list_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~R.Tried, ~RetryFfi.read_tried, r) == Wr.get_list.start(~R.Tried, ~Fr.get_tried, r) : Wr.Dec<List<&2, R.Tried>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %Equal.sym(Wr.Dec<R.Tried>, RetryFfi.read_tried(s), Fr.get_tried(s), rf.rd_tried(s)) : {Wr.get_list.go(~R.Tried, ~RetryFfi.read_tried, m, _) == Wr.get_list.go(~R.Tried, ~Fr.get_tried, m, Fr.get_tried(s)) : Wr.Dec<List<&2, R.Tried>>}
          rf.list_go(m, Fr.get_tried(s))
    case Wr.Bad{}:
      {==}

def rf.fo_max(len: Nat, tried: List<&2, R.Tried>, switches: Nat, base: Nat, r: Wr.Dec<Nat>) -> {RetryFfi.read_failover.max(len, tried, switches, base, r) == Fr.get_failover.policy(len, tried, Fr.get_policy.max(switches, base, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{max, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.fo_base(len: Nat, tried: List<&2, R.Tried>, switches: Nat, r: Wr.Dec<Nat>) -> {RetryFfi.read_failover.base(len, tried, switches, r) == Fr.get_failover.policy(len, tried, Fr.get_policy.base(switches, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{base, s}:
      rf.fo_max(len, tried, switches, base, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.fo_switches(len: Nat, tried: List<&2, R.Tried>, r: Wr.Dec<Nat>) -> {RetryFfi.read_failover.switches(len, tried, r) == Fr.get_failover.policy(len, tried, Fr.get_policy.switches(r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{switches, s}:
      rf.fo_base(len, tried, switches, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.fo_tried(len: Nat, r: Wr.Dec<List<&2, R.Tried>>) -> {RetryFfi.read_failover.tried(len, r) == Fr.get_failover.tried(len, r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{tried, s}:
      rf.fo_switches(len, tried, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.failover(r: Wr.Dec<Nat>) -> {RetryFfi.read_failover(r) == Fr.get_failover(r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{len, +s}:
      %Equal.sym(Wr.Dec<List<&2, R.Tried>>, Wr.get_list.start(~R.Tried, ~RetryFfi.read_tried, Wr.get_nat(s)), Wr.get_list.start(~R.Tried, ~Fr.get_tried, Wr.get_nat(s)), rf.list_start(Wr.get_nat(s))) : {RetryFfi.read_failover.tried(len, _) == Fr.get_failover.tried(len, Wr.get_list(~R.Tried, ~Fr.get_tried, s)) : Wr.Dec<Fr.Req>}
      rf.fo_tried(len, Wr.get_list(~R.Tried, ~Fr.get_tried, s))
    case Wr.Bad{}:
      {==}

def rf.stall(r: Wr.Dec<Nat>) -> {RetryFfi.read_stall(r) == Fr.get_stall(r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{idle, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.tag(t: Nat, s: String) -> {RetryFfi.read_req.tag(t, s) == Fr.get_req.tag(t, s) : Wr.Dec<Fr.Req>}:
  match t:
    case 0n:
      rf.facts(Wr.get_bool(s))
    case 1n:
      rf.wait(Wr.get_nat(s))
    case 2n:
      rf.failover(Wr.get_nat(s))
    case 3n:
      rf.stall(Wr.get_nat(s))
    case 4n+u:
      {==}

# the laws read every input as the entry's decoder does
def rf.rq(r: Wr.Dec<Nat>) -> {RetryFfi.read_req.go(r) == Fr.get_req.start(r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{t, s}:
      rf.tag(t, s)
    case Wr.Bad{}:
      {==}

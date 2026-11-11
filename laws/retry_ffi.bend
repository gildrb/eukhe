# eukhe: the laws of area retry_ffi (the entry of area retry, by the wire's spelling)

import Base
import ../bend/ffi_retry.bend as Fr
import ../bend/retry.bend as R
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./retry.bend as Retry

# ---- retry_ffi ----

# LAWS (R8, the retry entry spelled from the wire): bend/ffi_retry.bend
# `ffi`, the entry Rust calls for the classifier, the wait, the failover
# walk and the stall (crates/eukhe-bend/src/rules/retry.rs). The laws of
# laws/retry.bend (R7) read the entry through its own encoder and decoder;
# these spell every request and reply from the wire's primitives
# (bend/wire.bend), in the grammar of crates/eukhe-bend/WIRE.md, so an
# encoder and a decoder that agree with each other but not with that
# grammar fail them. Together they fix the entry's reply to every input
# string: a spelled request that fits the wire answers the model's
# decision (retry_ffi_entry_answers); one followed by more input answers
# the left-over error (retry_ffi_entry_left_over); any other input answers
# the malformed error (retry_ffi_entry_exact, retry_ffi_entry_left_over_exact
# and retry_ffi_entry_errors). The decisions themselves are fixed by the
# laws of laws/retry.bend (R1-R5). PROOF.bend proves these (as
# RetryFfi.<law>) with the lemmas of proof/retry_ffi/.

# Spelling
# --------

def spell_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

# a cause is its place in the declaration of R.Cause, from 0
def cause_num(k: R.Cause) -> Nat:
  match k:
    case R.Refusal{}:
      0n
    case R.Safety{}:
      1n
    case R.PaymentRequired{}:
      2n
    case R.Overloaded{}:
      3n
    case R.RateLimit{}:
      4n
    case R.ServerError{}:
      5n
    case R.Auth{}:
      6n
    case R.Permission{}:
      7n
    case R.InvalidRequest{}:
      8n
    case R.MalformedResponse{}:
      9n
    case R.StreamDrop{}:
      10n
    case R.StreamStalled{}:
      11n
    case R.StreamRepeating{}:
      12n
    case R.Unknown{}:
      13n

def spell_mcause(m: Maybe<&2, R.Cause>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{k}:
      Wr.put_nat(1n, Wr.put_nat(cause_num(k), rest))

def spell_tried(t: R.Tried, rest: String) -> String:
  match t:
    case R.Tried{at, wait}:
      Wr.put_nat(at, spell_mnat(wait, rest))

# the request Rust writes for q: its tag, then its fields in order, then
# rest (the input after it)
def spell_req(q: Fr.Req, rest: String) -> String:
  match q:
    case Fr.QClassify{f}:
      match f:
        case R.Facts{parked, limit, status, kind, text}:
          Wr.put_nat(0n, Wr.put_bool(parked, Wr.put_bool(limit, spell_mnat(status, spell_mcause(kind, Wr.put_bool(text, rest))))))
    case Fr.QWait{base, attempt, cap, draw, server}:
      Wr.put_nat(1n, Wr.put_nat(base, Wr.put_nat(attempt, Wr.put_nat(cap, Wr.put_nat(draw, spell_mnat(server, rest))))))
    case Fr.QFailover{len, tried, p}:
      match p:
        case R.Policy{switches, base, max}:
          Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~spell_tried, tried, Wr.put_nat(switches, Wr.put_nat(base, Wr.put_nat(max, rest))))))
    case Fr.QStall{idle}:
      Wr.put_nat(3n, Wr.put_nat(idle, rest))

def spell_delay(d: R.Delay) -> String:
  match d:
    case R.After{ms}:
      Wr.put_nat(0n, Wr.put_nat(ms, ""))
    case R.Refused{server, cap}:
      Wr.put_nat(1n, Wr.put_nat(server, Wr.put_nat(cap, "")))

def spell_switch(m: Maybe<&2, R.Switch>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{sw}:
      match sw:
        case R.Switch{to, delay}:
          Wr.put_nat(1n, Wr.put_nat(to, Wr.put_nat(delay, "")))

# the reply to q: the model's decision, spelled (the decisions are fixed by
# the requirement laws of laws/retry.bend: the classifier by R1's, the wait
# by R2's, the walk by R3's, the stall by stall_retry_doubles)
def spell_answer(q: Fr.Req) -> String:
  match q:
    case Fr.QClassify{f}:
      Wr.put_bool(R.retryable(f), "")
    case Fr.QWait{base, attempt, cap, draw, server}:
      spell_delay(R.retry_wait(base, attempt, cap, draw, server))
    case Fr.QFailover{len, tried, p}:
      spell_switch(R.next(len, tried, p))
    case Fr.QStall{idle}:
      Wr.put_nat(R.stall.next(idle), "")

# Laws
# ----

# LAW retry_ffi_entry_answers (R8): on every request Rust writes whose numbers fit the wire, spelled from the wire's primitives, the entry answers the model's decision spelled from them: the classifier's Bool, the wait's delay, the failover walk's next switch, the stall's next deadline
# EXCLUDES: an encoder and a decoder that agree with each other but not
#   with the wire (a swapped field, another cause order, the list count
#   after its items), a reply of another decision or in another spelling
law retry_ffi_entry_answers:
  for +q: Fr.Req
  for fits: {Retry.rs.req_fits(q) == True{} : Bool}
  {Fr.ffi(spell_req(q, "")) == spell_answer(q) : String}

# LAW retry_ffi_entry_exact (R8): every input the entry answers with a value (not the error form) is a spelled request whose numbers, and whose count of attempts, fit the wire
# EXCLUDES: a default decision for input that is no request (an unknown
#   tag, cause or Maybe mark, a missing field, a short list of attempts),
#   one with input left over, one with a Nat of 15 or more digits
law retry_ffi_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(Fr.ffi(s)) == False{} : Bool}
  exs q: Fr.Req
  {s == spell_req(q, "") : String} & {Retry.rs.req_fits(q) == True{} : Bool}

# LAW retry_ffi_entry_left_over (R8): a request that fits the wire, followed by more input, answers the left-over error form
# EXCLUDES: the input after the request ignored or read as part of it
law retry_ffi_entry_left_over:
  for +q: Fr.Req
  for +h: Char
  for +t: String
  for fits: {Retry.rs.req_fits(q) == True{} : Bool}
  {Fr.ffi(spell_req(q, SCon{h, t})) == Wr.err("retry: input left after the request") : String}

# LAW retry_ffi_entry_left_over_exact (R8): the entry answers the left-over error form only for a spelled request that fits the wire, followed by more input
# EXCLUDES: the left-over text for a malformed request (an over-long Nat
#   included)
law retry_ffi_entry_left_over_exact:
  for +s: String
  for e: {Fr.ffi(s) == Wr.err("retry: input left after the request") : String}
  exs q: Fr.Req
  exs h: Char
  exs t: String
  {s == spell_req(q, SCon{h, t}) : String} & {Retry.rs.req_fits(q) == True{} : Bool}

# LAW retry_ffi_entry_errors (R8): every error the entry answers is the malformed or the left-over error form; with retry_ffi_entry_exact and retry_ffi_entry_left_over_exact, every input that spells no request answers exactly "retry: malformed request"
# EXCLUDES: another error text (a made-up one, the text of another entry)
law retry_ffi_entry_errors:
  for +s: String
  for e: {LawsBase.wire_opens_err(Fr.ffi(s)) == True{} : Bool}
  {Bool.or(LawsBase.text_same(Fr.ffi(s), Wr.err("retry: malformed request")), LawsBase.text_same(Fr.ffi(s), Wr.err("retry: input left after the request"))) == True{} : Bool}

# LAW retry_ffi_entry_example: anchor: the strings Rust sends and the replies it reads: a 429 is retried; a wait of base 10, retry 4, cap 60, draw 95 is 35 ms (small numbers: the proven kernel unfolds them); the next of three tried providers returns to the first after 10 ms; a stall under 30 ms retries under 60; an unknown tag and input left over are refused
# EXCLUDES: another spelling of the requests or replies Rust reads
law retry_ffi_entry_example:
  {[Fr.ffi("0,FF1,429,0,F"), Fr.ffi("1,10,4,60,95,0,"), Fr.ffi("2,3,3,0,0,1,0,2,0,8,10,200,"), Fr.ffi("3,30,"), Fr.ffi("4,"), Fr.ffi("3,30,x")] == ["T", "0,35,", "1,0,10,", "60,", "E retry: malformed request", "E retry: input left after the request"] : List<&2, String>}

def read_facts.text(parked: Bool, limit: Bool, status: Maybe<&2, Nat>, kind: Maybe<&2, R.Cause>, r: Wr.Dec<Bool>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{text, s}:
      Wr.Got{Fr.QClassify{R.Facts{parked, limit, status, kind, text}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_facts.kind(parked: Bool, limit: Bool, status: Maybe<&2, Nat>, r: Wr.Dec<Maybe<&2, R.Cause>>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{kind, s}:
      read_facts.text(parked, limit, status, kind, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

# the cause of a number, from Refusal (0) on
def cause_of(t: Nat) -> Maybe<&2, R.Cause>:
  match t:
    case 0n:
      Some{R.Refusal{}}
    case 1n:
      Some{R.Safety{}}
    case 2n:
      Some{R.PaymentRequired{}}
    case 3n:
      Some{R.Overloaded{}}
    case 4n:
      Some{R.RateLimit{}}
    case 5n:
      Some{R.ServerError{}}
    case 6n:
      Some{R.Auth{}}
    case 7n:
      Some{R.Permission{}}
    case 8n:
      Some{R.InvalidRequest{}}
    case 9n:
      Some{R.MalformedResponse{}}
    case 10n:
      Some{R.StreamDrop{}}
    case 11n:
      Some{R.StreamStalled{}}
    case 12n:
      Some{R.StreamRepeating{}}
    case 13n:
      Some{R.Unknown{}}
    case 14n+u:
      None{}

def read_mcause.known(m: Maybe<&2, R.Cause>, s: String) -> Wr.Dec<Maybe<&2, R.Cause>>:
  match m:
    case Some{k}:
      Wr.Got{Some{k}, s}
    case None{}:
      Wr.Bad{}

def read_mcause.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, R.Cause>>:
  match r:
    case Wr.Got{t, s}:
      read_mcause.known(cause_of(t), s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_mcause.tag(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, R.Cause>>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{None{}, s}
        case 1n:
          read_mcause.some(Wr.get_nat(s))
        case 2n+k:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def read_mcause(s: String) -> Wr.Dec<Maybe<&2, R.Cause>>:
  read_mcause.tag(Wr.get_nat(s))

def read_facts.status(parked: Bool, limit: Bool, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{status, s}:
      read_facts.kind(parked, limit, status, read_mcause(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_mnat.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Some{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_mnat.tag(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{None{}, s}
        case 1n:
          read_mnat.some(Wr.get_nat(s))
        case 2n+k:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def read_mnat(s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  read_mnat.tag(Wr.get_nat(s))

def read_facts.limit(parked: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{limit, s}:
      read_facts.status(parked, limit, read_mnat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_facts(r: Wr.Dec<Bool>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{parked, s}:
      read_facts.limit(parked, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_failover.max(len: Nat, tried: List<&2, R.Tried>, switches: Nat, base: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{max, s}:
      Wr.Got{Fr.QFailover{len, tried, R.Policy{switches, base, max}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_failover.base(len: Nat, tried: List<&2, R.Tried>, switches: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{base, s}:
      read_failover.max(len, tried, switches, base, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_failover.switches(len: Nat, tried: List<&2, R.Tried>, r: Wr.Dec<Nat>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{switches, s}:
      read_failover.base(len, tried, switches, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_failover.tried(len: Nat, r: Wr.Dec<List<&2, R.Tried>>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{tried, s}:
      read_failover.switches(len, tried, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_tried.wait(at: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<R.Tried>:
  match r:
    case Wr.Got{wait, s}:
      Wr.Got{R.Tried{at, wait}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_tried.at(r: Wr.Dec<Nat>) -> Wr.Dec<R.Tried>:
  match r:
    case Wr.Got{at, s}:
      read_tried.wait(at, read_mnat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_tried(s: String) -> Wr.Dec<R.Tried>:
  read_tried.at(Wr.get_nat(s))

def read_failover(r: Wr.Dec<Nat>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{len, s}:
      read_failover.tried(len, Wr.get_list(~R.Tried, ~read_tried, s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_stall(r: Wr.Dec<Nat>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{idle, s}:
      Wr.Got{Fr.QStall{idle}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_wait.server(base: Nat, attempt: Nat, cap: Nat, draw: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{server, s}:
      Wr.Got{Fr.QWait{base, attempt, cap, draw, server}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_wait.draw(base: Nat, attempt: Nat, cap: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{draw, s}:
      read_wait.server(base, attempt, cap, draw, read_mnat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_wait.cap(base: Nat, attempt: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{cap, s}:
      read_wait.draw(base, attempt, cap, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_wait.attempt(base: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{attempt, s}:
      read_wait.cap(base, attempt, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_wait(r: Wr.Dec<Nat>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{base, s}:
      read_wait.attempt(base, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_req.tag(t: Nat, s: String) -> Wr.Dec<Fr.Req>:
  match t:
    case 0n:
      read_facts(Wr.get_bool(s))
    case 1n:
      read_wait(Wr.get_nat(s))
    case 2n:
      read_failover(Wr.get_nat(s))
    case 3n:
      read_stall(Wr.get_nat(s))
    case 4n+u:
      Wr.Bad{}

def read_req.go(r: Wr.Dec<Nat>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{t, s}:
      read_req.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request at the start of s, as the laws read it, and the rest
def read_req(s: String) -> Wr.Dec<Fr.Req>:
  read_req.go(Wr.get_nat(s))

# the jitter of a draw under a step: none under a step of 0, else the
# draw modulo the step (R2: full jitter in [0, step))
def wait_spec.jitter.pick(none: Bool, +step: Nat, +draw: Nat) -> Nat:
  match none:
    case True{}:
      0n
    case False{}:
      Nat.mod(draw, step)

def wait_spec.jitter(+step: Nat, +draw: Nat) -> Nat:
  wait_spec.jitter.pick(Nat.is_eq(step, 0n), step, draw)

# a server wait above a positive cap refuses the retry and names both;
# else the retry waits the longer of the jitter and the server's wait
def wait_spec.server(refuse: Bool, +jitter: Nat, +s: Nat, +cap: Nat) -> R.Delay:
  match refuse:
    case True{}:
      R.Refused{s, cap}
    case False{}:
      R.After{Nat.max(jitter, s)}

# the wait of a retry that drew `jitter`, after the server's wait, if any,
# under the cap (0: no cap)
def wait_spec.of(+jitter: Nat, server: Maybe<&2, Nat>, +cap: Nat) -> R.Delay:
  match server:
    case None{}:
      R.After{jitter}
    case Some{+s}:
      wait_spec.server(Bool.and(Bool.not(Nat.is_eq(cap, 0n)), Nat.is_gt(s, cap)), jitter, s, cap)

# the wait of retry `attempt` (1 for the first retry), as R2 states it
# (`retry_wait`, `RetryWait::of`): the jitter of the draw under the step
# (the base doubled per retry before this one, at most the cap), never
# before the server's wait, refused past a positive cap
def wait_spec(+base: Nat, +attempt: Nat, +cap: Nat, +draw: Nat, server: Maybe<&2, Nat>) -> R.Delay:
  wait_spec.of(wait_spec.jitter(Nat.min(Retry.rs.twice(Nat.sub(attempt, 1n), base), cap), draw), server, cap)

# the reply to q from the specs alone, spelled: the classifier of R1
# (rs.retryable), the wait of R2 (wait_spec), the walk of R3 (rs.next),
# the stall of R5 (twice the deadline)
def spec_answer(q: Fr.Req) -> String:
  match q:
    case Fr.QClassify{f}:
      Wr.put_bool(Retry.rs.retryable(f), "")
    case Fr.QWait{base, attempt, cap, draw, server}:
      spell_delay(wait_spec(base, attempt, cap, draw, server))
    case Fr.QFailover{len, tried, p}:
      spell_switch(Retry.rs.next(len, tried, p))
    case Fr.QStall{+idle}:
      Wr.put_nat(Nat.add(idle, idle), "")

# LAW retry_ffi_entry_reads_exact: every input the laws' reader reads whole as a request gets the reply the specs alone give that request (the classifier of R1, the wait of R2, the walk of R3, twice the stall's deadline), spelled from the wire's primitives; with retry_ffi_entry_malformed_exact and retry_ffi_entry_trailing_exact, the specs fix the entry's reply to every input string
# EXCLUDES: an input read whole answered with a decision the specs do not
#   give (a model that drifts from its spec, an entry that answers
#   another request or an error), whatever its spelling
law retry_ffi_entry_reads_exact:
  for +s: String
  for q: Fr.Req
  for rest: String
  for got: {read_req(s) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}
  for whole: {Wr.end(rest) == True{} : Bool}
  {Fr.ffi(s) == spec_answer(q) : String}

# LAW retry_wait_exact: the model's wait of a retry is the wait R2 states, for every base, attempt, cap, draw and server's wait
# EXCLUDES: a step that does not double or ignores the cap, a jitter at or
#   past the step, a retry before the server's wait, a refusal under no
#   cap or within it, a wait past a positive cap
law retry_wait_exact:
  for base: Nat
  for attempt: Nat
  for cap: Nat
  for draw: Nat
  for server: Maybe<&2, Nat>
  {R.retry_wait(base, attempt, cap, draw, server) == wait_spec(base, attempt, cap, draw, server) : R.Delay}

def rt_act(s: R.Step) -> R.Act:
  match s:
    case R.Step{a, j}:
      a

def rt_at(t: R.Tried) -> Nat:
  match t:
    case R.Tried{a, w}:
      a

def rt_base(p: R.Policy) -> Nat:
  match p:
    case R.Policy{s, b, m}:
      b

def rt_idle_at(i: R.Idle) -> Nat:
  match i:
    case R.IdleStall{a}:
      a
    case R.IdleClose{a}:
      a

def rt_job(s: R.Step) -> R.Job:
  match s:
    case R.Step{a, j}:
      j

def rt_late(y: R.Tally) -> Nat:
  match y:
    case R.Tally{s, l}:
      l

def rt_left(j: R.Job) -> Nat:
  match j:
    case R.NoJob{}:
      0n
    case R.Live{f, l}:
      l

def rt_live(j: R.Job) -> Bool:
  match j:
    case R.NoJob{}:
      False{}
    case R.Live{f, l}:
      True{}

def rt_max(p: R.Policy) -> Nat:
  match p:
    case R.Policy{s, b, m}:
      m

def rt_sends(y: R.Tally) -> Nat:
  match y:
    case R.Tally{s, l}:
      s

def rt_switches(p: R.Policy) -> Nat:
  match p:
    case R.Policy{s, b, m}:
      s

# LAW retry_terms_exact: the model's accessors the laws read are the fields they name: the
# failover budget, base and max of a policy, when a provider was tried, whether a job is live
# and its time left, a step's act and job, a tally's sends and late polls, when a stream ended
# EXCLUDES: an accessor that misreads a field (a budget of 0 read as 1) so that a law with the
#   model on both sides passes a wrong decision
law retry_terms_exact:
  for +p: R.Policy
  for +t: R.Tried
  for +j: R.Job
  for +s: R.Step
  for +y: R.Tally
  for +i: R.Idle
  {R.Policy.switches(p) == rt_switches(p) : Nat} & {R.Policy.base(p) == rt_base(p) : Nat} & {R.Policy.max(p) == rt_max(p) : Nat} & {R.Tried.at(t) == rt_at(t) : Nat} & {R.Job.live(j) == rt_live(j) : Bool} & {R.Job.left(j) == rt_left(j) : Nat} & {R.Step.act(s) == rt_act(s) : R.Act} & {R.Step.job(s) == rt_job(s) : R.Job} & {R.Tally.sends(y) == rt_sends(y) : Nat} & {R.Tally.late(y) == rt_late(y) : Nat} & {R.Idle.at(i) == rt_idle_at(i) : Nat}

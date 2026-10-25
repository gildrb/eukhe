# eukhe: the laws of area retry_ffi (the entry of area retry, by the wire's spelling)

import Base
import ../bend/ffi_retry.bend as Fr
import ../bend/retry.bend as R
import ../bend/wire.bend as Wr
import ./retry.bend as Retry

# ---- retry_ffi ----

# LAWS (R8, the retry entry spelled from the wire): bend/ffi_retry.bend
# `ffi`, the entry Rust calls for the classifier, the wait, the failover
# walk and the stall (crates/eukhe-bend/src/rules/retry.rs). The laws of
# laws/retry.bend (R7) read the entry through its own encoder and decoder;
# these spell every request and reply from the wire's primitives
# (bend/wire.bend) and read input with the laws' own reader, so a codec
# that is wrong on both sides alike still fails. PROOF.bend proves them
# (as RetryFfi.<law>) with the lemmas of proof/retry_ffi/.

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

# the request Rust writes for q: its tag, then its fields in order
def spell_req(q: Fr.Req) -> String:
  match q:
    case Fr.QClassify{f}:
      match f:
        case R.Facts{parked, limit, status, kind, text}:
          Wr.put_nat(0n, Wr.put_bool(parked, Wr.put_bool(limit, spell_mnat(status, spell_mcause(kind, Wr.put_bool(text, ""))))))
    case Fr.QWait{base, attempt, cap, draw, server}:
      Wr.put_nat(1n, Wr.put_nat(base, Wr.put_nat(attempt, Wr.put_nat(cap, Wr.put_nat(draw, spell_mnat(server, ""))))))
    case Fr.QFailover{len, tried, p}:
      match p:
        case R.Policy{switches, base, max}:
          Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~spell_tried, tried, Wr.put_nat(switches, Wr.put_nat(base, Wr.put_nat(max, ""))))))
    case Fr.QStall{idle}:
      Wr.put_nat(3n, Wr.put_nat(idle, ""))

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

# the reply to q: the model's decision, spelled
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

# The laws' reader
# ----------------

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

def read_facts.status(parked: Bool, limit: Bool, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Fr.Req>:
  match r:
    case Wr.Got{status, s}:
      read_facts.kind(parked, limit, status, read_mcause(s))
    case Wr.Bad{}:
      Wr.Bad{}

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

# Laws
# ----

# LAW retry_ffi_entry_answers: on every request Rust writes whose numbers fit the wire, spelled from the wire's primitives, the entry answers the model's decision spelled from them: the classifier's Bool, the wait's delay, the failover walk's next switch, the stall's next deadline
# EXCLUDES: an encoder and a decoder that agree with each other but not
#   with the wire (a swapped field, another cause order, the list count
#   after its items), a reply of another decision or in another spelling
law retry_ffi_entry_answers:
  for +q: Fr.Req
  for fits: {Retry.rs.req_fits(q) == True{} : Bool}
  {Fr.ffi(spell_req(q)) == spell_answer(q) : String}

# LAW retry_ffi_entry_malformed_exact: every input the laws' reader reads no request from gets exactly the error form 'E ', then "retry: malformed request" (the text Rust's Reader reports)
# EXCLUDES: a default decision for input that is no request (an unknown
#   tag, cause or Maybe mark), another error text
law retry_ffi_entry_malformed_exact:
  for +s: String
  for no: {read_req(s) == Wr.Bad{} : Wr.Dec<Fr.Req>}
  {Fr.ffi(s) == SCon{'E', SCon{' ', "retry: malformed request"}} : String}

# LAW retry_ffi_entry_trailing_exact: every input the laws' reader reads a request from with input left over gets exactly the error form 'E ', then "retry: input left after the request"
# EXCLUDES: a decision for a request followed by garbage, another error
#   text
law retry_ffi_entry_trailing_exact:
  for +s: String
  for q: Fr.Req
  for rest: String
  for got: {read_req(s) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}
  for left: {Wr.end(rest) == False{} : Bool}
  {Fr.ffi(s) == SCon{'E', SCon{' ', "retry: input left after the request"}} : String}

# LAW retry_ffi_entry_example: anchor: the strings Rust sends and the replies it reads: a 429 is retried; a wait of base 10, retry 4, cap 60, draw 95 is 35 ms (small numbers: the proven kernel unfolds them); the next of three tried providers returns to the first after 10 ms; a stall under 30 ms retries under 60; an unknown tag and input left over are refused
# EXCLUDES: another spelling of the requests or replies Rust reads
law retry_ffi_entry_example:
  {[Fr.ffi("0,FF1,429,0,F"), Fr.ffi("1,10,4,60,95,0,"), Fr.ffi("2,3,3,0,0,1,0,2,0,8,10,200,"), Fr.ffi("3,30,"), Fr.ffi("4,"), Fr.ffi("3,30,x")] == ["T", "0,35,", "1,0,10,", "60,", "E retry: malformed request", "E retry: input left after the request"] : List<&2, String>}

# LAW retry_length_exact: the model's `length` of the providers tried, which the laws' request
# fit (`rs.req_fits`) reads, is the number of providers tried
# EXCLUDES: a fit check that a wrong `length` makes refuse a request Rust sends (or accept one
#   past the wire), which a second fresh adversary noted no law pinned
law retry_length_exact:
  for +ts: List<&2, R.Tried>
  {R.length(ts) == List.length(&2, R.Tried, ts) : Nat}

# The model's accessors, pinned
# -----------------------------
# A third fresh adversary (SpecCheckRetry3) filled `R.Policy.switches` to
# read a budget of 0 as 1 (`ffi("2,2,1,0,0,0,10,200,")` switching to
# provider 1 instead of answering no switch) and every law checked: the
# laws' own failover spec (laws/retry.bend `rs.next`) reads the policy
# through the model's accessors, so failover_exact had the model on both
# sides. The accessors the laws read are pinned here.

def rt_switches(p: R.Policy) -> Nat:
  match p:
    case R.Policy{s, b, m}:
      s

def rt_base(p: R.Policy) -> Nat:
  match p:
    case R.Policy{s, b, m}:
      b

def rt_max(p: R.Policy) -> Nat:
  match p:
    case R.Policy{s, b, m}:
      m

def rt_at(t: R.Tried) -> Nat:
  match t:
    case R.Tried{a, w}:
      a

def rt_live(j: R.Job) -> Bool:
  match j:
    case R.NoJob{}:
      False{}
    case R.Live{f, l}:
      True{}

def rt_left(j: R.Job) -> Nat:
  match j:
    case R.NoJob{}:
      0n
    case R.Live{f, l}:
      l

def rt_act(s: R.Step) -> R.Act:
  match s:
    case R.Step{a, j}:
      a

def rt_job(s: R.Step) -> R.Job:
  match s:
    case R.Step{a, j}:
      j

def rt_sends(y: R.Tally) -> Nat:
  match y:
    case R.Tally{s, l}:
      s

def rt_late(y: R.Tally) -> Nat:
  match y:
    case R.Tally{s, l}:
      l

def rt_idle_at(i: R.Idle) -> Nat:
  match i:
    case R.IdleStall{a}:
      a
    case R.IdleClose{a}:
      a

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

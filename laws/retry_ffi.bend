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

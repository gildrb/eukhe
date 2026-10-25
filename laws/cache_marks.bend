# eukhe: the laws of area cache_marks

import Base
import ../bend/cache_marks.bend as Cm
import ../bend/ffi_cache_marks.bend as FCm
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (A1) The cache-mark budget of one provider request
# --------------------------------------------------
# bend/cache_marks.bend, run as the compiled core by
# bend/ffi_cache_marks.bend (eukhe-bend rules/cache_marks.rs; asked by the
# eukhe-ai request builders of Anthropic Messages, OpenAI-compatible
# Completions and Bedrock Converse). Every input is free: any count of
# marked blocks, any count of placed marks, any list of wanted marks.
#
# R1: a request that marks more than 3 user text blocks fails with exactly
#     "Too many cache breakpoints: the request marks <n> blocks, at most 3
#     are allowed" (n in decimal); a request that marks at most 3 does not.
# R2: a request carries at most 4 cache marks. After `placed` marks on its
#     messages, 4 - placed slots are left (none when placed >= 4). The
#     optional marks are asked in the provider's priority order, one answer
#     per mark: a mark the request does not want is never granted and
#     spends no slot; the k-th wanted mark (counting from 0) is granted
#     exactly when k is below the slots left.
# R3: the entry answers each request Rust writes (every number and count
#     within the wire) with the answer of R1 or R2, reads exactly the
#     request and nothing after it, and answers any other input with the
#     exact error form `E cache_marks: malformed request`.

# Spec helpers
# ------------

def sp_excess.of(fits: Bool, +n: Nat) -> Maybe<&2, String>:
  match fits:
    case True{}:
      None{}
    case False{}:
      Some{String.concat(["Too many cache breakpoints: the request marks ", Nat.show(n), " blocks, at most 3 are allowed"])}

# R1: the error of a request that marks n user text blocks
def sp_excess(+n: Nat) -> Maybe<&2, String>:
  sp_excess.of(Nat.is_le(n, 3n), n)

def sp_bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# R2: each answer, with k wanted marks before it and `free` slots
def sp_grant.go(ws: List<&2, Bool>, +k: Nat, +free: Nat) -> List<&2, Bool>:
  match ws:
    case Nil{}:
      Nil{}
    case +w <> t:
      Bool.and(w, Nat.is_lt(k, free)) <> sp_grant.go(t, Nat.add(sp_bit(w), k), free)

# R2: the answers after `placed` marks
def sp_grant(placed: Nat, ws: List<&2, Bool>) -> List<&2, Bool>:
  sp_grant.go(ws, 0n, Nat.sub(4n, placed))

# R3: the spelling of a request and of its reply

def sp_w_bools(xs: List<&2, Bool>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      Wr.put_bool(x, sp_w_bools(t, rest))

def sp_w_req(q: FCm.Req, rest: String) -> String:
  match q:
    case FCm.QExcess{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case FCm.QGrant{p, +ws}:
      Wr.put_nat(1n, Wr.put_nat(p, Wr.put_nat(List.length(&2, Bool, ws), sp_w_bools(ws, rest))))

def sp_w_excess(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{e}:
      Wr.put_nat(1n, Wr.put_str(e, ""))

def sp_w_reply(q: FCm.Req) -> String:
  match q:
    case FCm.QExcess{n}:
      sp_w_excess(sp_excess(n))
    case FCm.QGrant{p, ws}:
      +g = sp_grant(p, ws)
      Wr.put_nat(List.length(&2, Bool, g), sp_w_bools(g, ""))

# every number and count of the request fits the wire
def sp_fit_req(q: FCm.Req) -> Bool:
  match q:
    case FCm.QExcess{n}:
      LawsBase.wire_fits(n)
    case FCm.QGrant{p, ws}:
      Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(List.length(&2, Bool, ws)))

# Laws: the budget
# ----------------

# LAW cache_marks_excess (R1): the error of every count of marked blocks is
# the spec's: none up to 3, else the fixed text with the count
# EXCLUDES: a limit of 4 (the end mark forgotten), a limit off by one, a
#   text without the count, another count in the text
law cache_marks_excess:
  for +n: Nat
  {Cm.excess(n) == sp_excess(n) : Maybe<&2, String>}

# LAW cache_marks_grant (R2): the answers for every count of placed marks
# and every list of wanted marks are the spec's
# EXCLUDES: an unwanted mark that spends a slot, a mark granted past the
#   slots left, a later mark preferred, an answer dropped or added, a
#   budget of 3 or 5, placed marks not subtracted
law cache_marks_grant:
  for +placed: Nat
  for +ws: List<&2, Bool>
  {Cm.grant(placed, ws) == sp_grant(placed, ws) : List<&2, Bool>}

# LAW cache_marks_example (R1, R2): anchor: the vectors of the Rust tests:
# three marks after one placed, none after four, unwanted marks skipped,
# the error at 4 marked blocks and none at 3
# EXCLUDES: a spec that drifts from the Rust it replaced
law cache_marks_example:
  {(Cm.grant(1n, [True{}, True{}, True{}, True{}]), (Cm.grant(4n, [True{}]), (Cm.grant(2n, [False{}, True{}, False{}, True{}, True{}]), (Cm.excess(3n), Cm.excess(4n))))) == ([True{}, True{}, True{}, False{}], ([False{}], ([False{}, True{}, False{}, True{}, False{}], (None{}, Some{"Too many cache breakpoints: the request marks 4 blocks, at most 3 are allowed"})))) : List<&2, Bool> & (List<&2, Bool> & (List<&2, Bool> & (Maybe<&2, String> & Maybe<&2, String>)))}

# Laws: the entry (R3)
# --------------------

# LAW cache_marks_entry_answers (R3): the entry answers every request Rust
# spells, every number within the wire, with the spelled answer of the spec
# EXCLUDES: the questions swapped, the counts swapped, a wanted mark read
#   as unwanted, a default
law cache_marks_entry_answers:
  for +q: FCm.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FCm.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW cache_marks_entry_reads (R3): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law cache_marks_entry_reads:
  for +q: FCm.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FCm.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FCm.Req>}

# LAW cache_marks_entry_exact (R3): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown question, a
#   malformed field, input left over)
law cache_marks_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCm.ffi(s)) == False{} : Bool}
  exs r: FCm.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW cache_marks_entry_refuses (R3): every error the entry answers is
# exactly `E cache_marks: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law cache_marks_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FCm.ffi(s)) == True{} : Bool}
  {FCm.ffi(s) == Wr.err("cache_marks: malformed request") : String}

# LAW cache_marks_entry_example (R3): anchor: the wire strings Rust sends
# and the replies it reads; an unknown question, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law cache_marks_entry_example:
  {[FCm.ffi("0,4,"), FCm.ffi("0,3,"), FCm.ffi("1,2,3,TFT"), FCm.ffi("2,0,"), FCm.ffi("0,3,x")] == ["1,77,Too many cache breakpoints: the request marks 4 blocks, at most 3 are allowed", "0,", "3,TFT", Wr.err("cache_marks: malformed request"), Wr.err("cache_marks: malformed request")] : List<&2, String>}

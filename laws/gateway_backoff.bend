# eukhe: the laws of area gateway_backoff

import Base
import ../bend/gateway_backoff.bend as Gb
import ../bend/ffi_gateway_backoff.bend as FGb
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (D1) The Signal gateway's reconnect wait
# ----------------------------------------
# bend/gateway_backoff.bend, run as the compiled core by
# bend/ffi_gateway_backoff.bend (crates/eukhe-gateway link.rs, gateway.rs:
# at every failed attempt to reach the daemon). Every input is free: any
# last wait.
#
# R1: the first wait is 250 ms.
# R2: each next wait doubles the last one, but never passes 10 s
#     (10000 ms): a doubled wait past it is 10 s.
# R3: the entry answers each request Rust writes (the last wait, if any,
#     within the wire) with the wait of R1-R2, reads exactly the request
#     and nothing after it, and answers any other input with the exact
#     error form `E gateway_backoff: malformed request`.

# Spec helpers
# ------------

def gb_cap(b: Bool, x: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      10000n

# R1, R2: the wait after `last`
def gb_wait(last: Maybe<&2, Nat>) -> Nat:
  match last:
    case None{}:
      250n
    case Some{d}:
      +x = Nat.mul(2n, d)
      gb_cap(Nat.is_le(x, 10000n), x)

def gb_w_req(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{d}:
      Wr.put_nat(1n, Wr.put_nat(d, rest))

# the last wait fits the wire
def gb_fit(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{d}:
      LawsBase.wire_fits(d)

# Laws: the wait
# --------------

# LAW gateway_backoff_spec (R1, R2): the wait after every last wait is the
# spec's: 250 ms first, then the last one doubled, at most 10 s
# EXCLUDES: another first wait, a wait that does not grow, a cap other
#   than 10 s, a doubled wait kept past the cap
law gateway_backoff_spec:
  for m: Maybe<&2, Nat>
  {Gb.next(m) == gb_wait(m) : Nat}

# LAW gateway_backoff_bounded (R2): no wait passes 10 s, whatever the last
# one was
# EXCLUDES: a cap that a large last wait escapes
law gateway_backoff_bounded:
  for m: Maybe<&2, Nat>
  {Nat.is_le(Gb.next(m), 10000n) == True{} : Bool}

# LAW gateway_backoff_example (R1, R2): anchor: the waits Rust took before:
# 250, 500, 1000, ..., 8000, then 10 s, and 10 s again
# EXCLUDES: a spec that drifts from the Rust it replaced
law gateway_backoff_example:
  {[Gb.next(None{}), Gb.next(Some{250n}), Gb.next(Some{500n}), Gb.next(Some{4000n}), Gb.next(Some{5000n}), Gb.next(Some{8000n}), Gb.next(Some{10000n})] == [250n, 500n, 1000n, 8000n, 10000n, 10000n, 10000n] : List<&2, Nat>}

# Laws: the entry (R3)
# --------------------

# LAW gateway_backoff_entry_answers (R3): the entry answers every request
# Rust spells (a last wait within the wire) with the spec's wait
# EXCLUDES: the last wait misread, a default, a first wait for a last one
law gateway_backoff_entry_answers:
  for +m: Maybe<&2, Nat>
  for h: {gb_fit(m) == True{} : Bool}
  {FGb.ffi(gb_w_req(m, "")) == Wr.put_nat(gb_wait(m), "") : String}

# LAW gateway_backoff_entry_reads (R3): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law gateway_backoff_entry_reads:
  for +m: Maybe<&2, Nat>
  for +rest: String
  for h: {gb_fit(m) == True{} : Bool}
  {FGb.get_req(gb_w_req(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Nat>>}

# LAW gateway_backoff_entry_exact (R3): every input the entry does not
# answer with the error form is a spelled request that fits the wire
# EXCLUDES: a wait answered on input that is no request
law gateway_backoff_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FGb.ffi(s)) == False{} : Bool}
  exs m: Maybe<&2, Nat>
  {s == gb_w_req(m, "") : String} & {gb_fit(m) == True{} : Bool}

# LAW gateway_backoff_entry_refuses (R3): every error the entry answers is
# exactly `E gateway_backoff: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law gateway_backoff_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FGb.ffi(s)) == True{} : Bool}
  {FGb.ffi(s) == Wr.err("gateway_backoff: malformed request") : String}

# LAW gateway_backoff_entry_example (R3): anchor: the wire strings Rust
# sends and the replies it reads; an unknown tag and input left over
# EXCLUDES: tags in another order
law gateway_backoff_entry_example:
  {[FGb.ffi("0,"), FGb.ffi("1,250,"), FGb.ffi("1,8000,"), FGb.ffi("2,"), FGb.ffi("0,0,")] == ["250,", "500,", "10000,", Wr.err("gateway_backoff: malformed request"), Wr.err("gateway_backoff: malformed request")] : List<&2, String>}

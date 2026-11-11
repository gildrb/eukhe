# eukhe: the laws of area infer_force

import Base
import ../bend/infer.bend as If
import ../bend/infer_force.bend as M
import ../bend/ffi_infer_force.bend as FF
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S6.2) A forced tool call, one attempt at a time
# ------------------------------------------------
# The model `force` in bend/infer.bend section 2;
# the harness asks the compiled core (bend/ffi_infer_force.bend) for each
# request's native flag and for the step after each reply. Every input is
# free: any attempt, retries, provider support, replies.
#
# R1: the first attempt of a forced call sets the native flag only when
#     the provider supports it and it is free; every retry sets it when
#     the provider supports it (laws/infer.bend: force_first_flag,
#     force_retry_flag).
# R2: a reply that calls the tool ends the forced call; a miss retries
#     while retries remain, so a call makes at most 1 + r attempts and
#     fails after the last miss (force_bounded, force_reports).
# R3: the entry answers each request Rust writes (crates/eukhe-bend
#     src/rules/infer_force.rs: a flag request `0,i,sup,free`, a step
#     request `1,i,r,c`) with the model's flag or step; every other input
#     gets exactly the error form 'E ', then "infer_force: malformed
#     request".
# R1 and R2 hold for the steps the harness takes through
# infer_force_steps (driven over the replies, they are `force`); R3 is
# infer_force_ffi_flag, infer_force_ffi_after, infer_force_ffi_reads and
# infer_force_ffi_refuses.

# the attempts as the harness drives the steps from attempt i: each
# request's flag, until a reply calls the tool, a miss fails the call, or
# the replies run out (a missing reply is no call)
def drive.next(n: M.Next, +f: Bool, more: List<&2, If.Try> & If.Forced) -> List<&2, If.Try> & If.Forced:
  match n:
    case M.Hit{}:
      ([If.Try{f}], If.Called{})
    case M.Again{}:
      (ts, o) = more
      (If.Try{f} <> ts, o)
    case M.Fails{}:
      ([If.Try{f}], If.Missed{})

def drive(replies: List<&2, Bool>, +i: Nat, +r: Nat, +sup: Bool, +free: Bool) -> List<&2, If.Try> & If.Forced:
  match replies:
    case Nil{}:
      ([If.Try{M.flag(i, sup, free)}], If.Missed{})
    case c <> rest:
      drive.next(M.after(i, r, c), M.flag(i, sup, free), drive(rest, 1n+i, r, sup, free))

# LAW infer_force_steps: the steps the harness takes, driven over the replies from the first attempt, are the forced call `force`: every law of `force` holds for them
law infer_force_steps:
  for replies: List<&2, Bool>
  for +r: Nat
  for +sup: Bool
  for +free: Bool
  {drive(replies, 0n, r, sup, free) == If.force(r, replies, sup, free) : List<&2, If.Try> & If.Forced}

# The entry (bend/ffi_infer_force.bend)
# -------------------------------------
# The spellers write what Rust writes, with the wire primitives only.

# the native flag of attempt i
def spell_flag(i: Nat, sup: Bool, free: Bool) -> String:
  Wr.put_nat(0n, Wr.put_nat(i, Wr.put_bool(sup, Wr.put_bool(free, ""))))

# the step after the reply c to attempt i, with r retries
def spell_after(i: Nat, r: Nat, c: Bool) -> String:
  Wr.put_nat(1n, Wr.put_nat(i, Wr.put_nat(r, Wr.put_bool(c, ""))))

# the step Rust reads: 0 called | 1 retry | 2 failed
def spell_next(n: M.Next) -> String:
  match n:
    case M.Hit{}:
      Wr.put_nat(0n, "")
    case M.Again{}:
      Wr.put_nat(1n, "")
    case M.Fails{}:
      Wr.put_nat(2n, "")

# a request Rust writes: the flag of attempt i, or the step after it
def spell_ask(q: FF.Req) -> String:
  match q:
    case FF.QFlag{i, sup, free}:
      spell_flag(i, sup, free)
    case FF.QAfter{i, r, c}:
      spell_after(i, r, c)

# every number of a request fits the wire
def ask_fits(q: FF.Req) -> Bool:
  match q:
    case FF.QFlag{i, sup, free}:
      LawsBase.wire_fits(i)
    case FF.QAfter{i, r, c}:
      Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(r))

# LAW infer_force_ffi_flag: for every attempt that fits the wire and every provider, the entry answers the model's native flag
law infer_force_ffi_flag:
  for +i: Nat
  for +sup: Bool
  for +free: Bool
  for fits: {LawsBase.wire_fits(i) == True{} : Bool}
  {FF.ffi(spell_flag(i, sup, free)) == Wr.put_bool(M.flag(i, sup, free), "") : String}

# LAW infer_force_ffi_after: for every attempt and retries that fit the wire and every reply, the entry answers the model's step after it
law infer_force_ffi_after:
  for +i: Nat
  for +r: Nat
  for +c: Bool
  for fits: {Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(r)) == True{} : Bool}
  {FF.ffi(spell_after(i, r, c)) == spell_next(M.after(i, r, c)) : String}

# LAW infer_force_ffi_reads (R3): every input the entry does not answer
# with the error form (a reply that opens with 'E') is a request Rust
# writes, spelled by spell_flag or spell_after, whose numbers fit the wire
# EXCLUDES: an answer for an input that is no request: input left over, an
#   unknown tag, a short or malformed field, a number past the wire's 14
#   digits, a second spelling of a request
law infer_force_ffi_reads:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FF.ffi(s)) == False{} : Bool}
  exs q: FF.Req
  {s == spell_ask(q) : String} & {ask_fits(q) == True{} : Bool}

# LAW infer_force_ffi_refuses (R3): every error the entry answers is
# exactly the error form 'E ', then "infer_force: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form
law infer_force_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FF.ffi(s)) == True{} : Bool}
  {FF.ffi(s) == SCon{'E', SCon{' ', "infer_force: malformed request"}} : String}

# LAW infer_force_ffi_example: anchor: the bytes Rust sends and reads: a first request sets the flag only when supported and free, a retry when supported; a miss within the retries retries, past them fails, a call ends; an unknown tag and input left over are refused
law infer_force_ffi_example:
  {FF.ffi("0,0,TT") == "T" : String} &
  {FF.ffi("0,0,TF") == "F" : String} &
  {FF.ffi("0,1,TF") == "T" : String} &
  {FF.ffi("0,2,FT") == "F" : String} &
  {FF.ffi("1,0,2,F") == "1," : String} &
  {FF.ffi("1,1,2,F") == "1," : String} &
  {FF.ffi("1,2,2,F") == "2," : String} &
  {FF.ffi("1,0,0,F") == "2," : String} &
  {FF.ffi("1,2,2,T") == "0," : String} &
  {FF.ffi("2,") == SCon{'E', SCon{' ', "infer_force: malformed request"}} : String} &
  {FF.ffi("0,0,TTT") == SCon{'E', SCon{' ', "infer_force: malformed request"}} : String}

# eukhe: the laws of area infer_force

import Base
import ../bend/infer.bend as If
import ../bend/infer_force.bend as M
import ../bend/ffi_infer_force.bend as FF
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S6.2) A forced tool call, one attempt at a time
# ------------------------------------------------
# docs/inference.md S6.2, the model `force` in bend/infer.bend section 2;
# the harness asks the compiled core (bend/ffi_infer_force.bend) for each
# request's native flag and for the step after each reply. Every input is
# free: any attempt, retries, provider support, replies.

# The steps, independently: the first attempt (0) sets the native flag
# only when the provider supports it and it is free, a retry whenever the
# provider supports it; a reply that calls the tool ends the call, a miss
# on attempt i (counted from 0) retries when attempt i + 1 (counted from
# 1) is within the retries, else the call fails
def flag_spec(i: Nat, sup: Bool, free: Bool) -> Bool:
  match i:
    case 0n:
      match sup:
        case True{}:
          free
        case False{}:
          False{}
    case 1n+j:
      sup

def after_spec.miss(within: Bool) -> M.Next:
  match within:
    case True{}:
      M.Again{}
    case False{}:
      M.Fails{}

def after_spec(i: Nat, r: Nat, c: Bool) -> M.Next:
  match c:
    case True{}:
      M.Hit{}
    case False{}:
      after_spec.miss(Nat.is_le(1n+i, r))

# LAW infer_force_flag_exact: the native flag of attempt i is exactly: on the first attempt the provider's support and the flag being free, on every retry the provider's support
law infer_force_flag_exact:
  for i: Nat
  for sup: Bool
  for free: Bool
  {M.flag(i, sup, free) == flag_spec(i, sup, free) : Bool}

# LAW infer_force_after_exact: the step after a reply is exactly: a call ends the forced call; a miss retries when the attempt (counted from 1) is within the retries, else the call fails
law infer_force_after_exact:
  for +i: Nat
  for +r: Nat
  for c: Bool
  {M.after(i, r, c) == after_spec(i, r, c) : M.Next}

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

# Reader: the requests the entry accepts, read with the wire primitives
type Ask is Data:
  AFlag{i: Nat, sup: Bool, free: Bool}
  AAfter{i: Nat, r: Nat, c: Bool}

def read_flag.free(i: Nat, sup: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{free, s}:
      Wr.Got{AFlag{i, sup, free}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_flag.sup(i: Nat, d: Wr.Dec<Bool>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{sup, s}:
      read_flag.free(i, sup, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_flag(d: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{i, s}:
      read_flag.sup(i, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_after.called(i: Nat, r: Nat, d: Wr.Dec<Bool>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{c, s}:
      Wr.Got{AAfter{i, r, c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_after.retries(i: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{r, s}:
      read_after.called(i, r, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_after(d: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{i, s}:
      read_after.retries(i, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tag(t: Nat, s: String) -> Wr.Dec<Ask>:
  match t:
    case 0n:
      read_flag(Wr.get_nat(s))
    case 1n:
      read_after(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def read_ask.go(d: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{t, s}:
      read_ask.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: Ask) -> Maybe<&2, Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(d: Wr.Dec<Ask>) -> Maybe<&2, Ask>:
  match d:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, Ask>:
  read_ask.whole(read_ask.go(Wr.get_nat(s)))

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

# LAW infer_force_ffi_malformed_exact: every input that is not exactly one request gets exactly the error form 'E ', then "infer_force: malformed request"
law infer_force_ffi_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, Ask>}
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

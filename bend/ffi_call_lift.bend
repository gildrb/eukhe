# ffi_call_lift: the entry of the compiled Bend core that lifts stored
# tool calls to the current dialect of their families
# (bend/call_lift.bend, the shipped table `table()`; Rust: eukhe-bend
# rules/call_lift.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  the calls of a transcript, in order (List): each its family
#            (String), its rev (String) and its argument names in order
#            (List<String>)
#   reply    one lift per call, in order (List): 0 unknown | 1 current |
#            2 stranded | 3 lifted: the rev (String), the arguments (List:
#            0 kept: the stored index (Nat), the name (String) | 1 added:
#            the name, the JSON value (String each)), the receipts (List:
#            0 renamed: from, to | 1 clashed: from, to | 2 filled: the
#            name; Strings)
#
# Each call's lift is spelled by itself, in the order of the calls, so
# the reply of a transcript is its calls' spellings one after another.
# Malformed input, or input left after the request, answers
# `E call_lift: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./call_lift.bend as Cl

# Requests
# --------

def get_call.keys(f: String, r: String, d: W.Dec<List<&2, String>>) -> W.Dec<Cl.Call>:
  match d:
    case W.Got{ks, s}:
      W.Got{Cl.Call{f, r, ks}, s}
    case W.Bad{}:
      W.Bad{}

def get_call.rev(f: String, d: W.Dec<String>) -> W.Dec<Cl.Call>:
  match d:
    case W.Got{r, s}:
      get_call.keys(f, r, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_call.fam(d: W.Dec<String>) -> W.Dec<Cl.Call>:
  match d:
    case W.Got{f, s}:
      get_call.rev(f, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

# a call at the start of s
def get_call(s: String) -> W.Dec<Cl.Call>:
  get_call.fam(W.get_str(s))

# the request at the start of s
def get_req(s: String) -> W.Dec<List<&2, Cl.Call>>:
  W.get_list(~Cl.Call, ~get_call, s)

# Replies
# -------

def put_arg(a: Cl.Arg, rest: String) -> String:
  match a:
    case Cl.Kept{i, k}:
      W.put_nat(0n, W.put_nat(i, W.put_str(k, rest)))
    case Cl.Added{k, j}:
      W.put_nat(1n, W.put_str(k, W.put_str(j, rest)))

def put_receipt(x: Cl.Receipt, rest: String) -> String:
  match x:
    case Cl.Renamed{a, b}:
      W.put_nat(0n, W.put_str(a, W.put_str(b, rest)))
    case Cl.Clashed{a, b}:
      W.put_nat(1n, W.put_str(a, W.put_str(b, rest)))
    case Cl.Filled{k}:
      W.put_nat(2n, W.put_str(k, rest))

# the spelling of a lift, then rest
def put_lift(l: Cl.Lift, rest: String) -> String:
  match l:
    case Cl.Unknown{}:
      W.put_nat(0n, rest)
    case Cl.Current{}:
      W.put_nat(1n, rest)
    case Cl.Stranded{}:
      W.put_nat(2n, rest)
    case Cl.Lifted{r, args, rs}:
      W.put_nat(3n, W.put_str(r, W.put_list(~Cl.Arg, ~put_arg, args, W.put_list(~Cl.Receipt, ~put_receipt, rs, rest))))

# the lifts of the calls cs by table t, each spelled, then rest
def put_lifts(+t: List<&2, Cl.Fam>, cs: List<&2, Cl.Call>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case Con{c, more}:
      put_lift(Cl.lift(t, c), put_lifts(t, more, rest))

# the reply of a request: how many lifts, then each
def answer(+cs: List<&2, Cl.Call>) -> String:
  W.put_nat(List.length(&2, Cl.Call, cs), put_lifts(Cl.table(), cs, ""))

def ffi.done(cs: List<&2, Cl.Call>, end: Bool) -> String:
  match end:
    case True{}:
      answer(cs)
    case False{}:
      W.err("call_lift: malformed request")

def ffi.got(r: W.Dec<List<&2, Cl.Call>>) -> String:
  match r:
    case W.Got{cs, +s}:
      ffi.done(cs, W.end(s))
    case W.Bad{}:
      W.err("call_lift: malformed request")

# the entry: decode the calls, answer their lifts
def ffi(input: String) -> String:
  ffi.got(get_req(input))

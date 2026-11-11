# harness (spec): the wire of the call_lift entry (bend/ffi_call_lift.bend,
# crates/eukhe-bend/WIRE.md) restated without the entry's code: how Rust
# spells a request, which requests fit the wire, the reply the lifts of
# spec/harness/lift.bend spell, and the reader of a request. The laws of
# area call_lift state that the entry answers it. A spec: the shipped
# code never calls it.
#
# W1: a request is the count of the calls, then each call: its family,
#     its rev, then its argument names (a list of strings).
# W2: a reply is the count of the lifts, then each lift in the order of
#     the calls: 0 unknown | 1 current | 2 stranded | 3 lifted, then the
#     rev, the arguments (count, then each: 0 kept, the index, the name |
#     1 added, the name, the JSON) and the receipts (count, then each:
#     0 renamed or 1 clashed, from, to | 2 filled, the name).
# W3: anything else is no request.

import Base
import ../../bend/call_lift.bend as Cl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ./lift.bend as Sp

# Requests (W1)
# -------------

def w_call(c: Cl.Call, rest: String) -> String:
  match c:
    case Cl.Call{f, r, ks}:
      Wr.put_str(f, Wr.put_str(r, Wr.put_list(~String, ~Wr.put_str, ks, rest)))

# the calls, one after another, then rest
def w_calls(cs: List<&2, Cl.Call>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case Con{c, more}:
      w_call(c, w_calls(more, rest))

# a request: the count of the calls, then the calls
def w_req(+cs: List<&2, Cl.Call>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cl.Call, cs), w_calls(cs, rest))

def fit_call(c: Cl.Call) -> Bool:
  match c:
    case Cl.Call{+f, +r, +ks}:
      Bool.and(LawsBase.wire_fits(String.length(f)), Bool.and(LawsBase.wire_fits(String.length(r)), LawsBase.wire_strs_fit(ks)))

def fit_calls(cs: List<&2, Cl.Call>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, more}:
      Bool.and(fit_call(c), fit_calls(more))

# a request fits the wire: its count, and every name of every call
def fit_req(+cs: List<&2, Cl.Call>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Cl.Call, cs)), fit_calls(cs))

# Replies (W2)
# ------------

def w_arg(a: Cl.Arg, rest: String) -> String:
  match a:
    case Cl.Kept{i, k}:
      Wr.put_nat(0n, Wr.put_nat(i, Wr.put_str(k, rest)))
    case Cl.Added{k, j}:
      Wr.put_nat(1n, Wr.put_str(k, Wr.put_str(j, rest)))

def w_args.items(a: List<&2, Cl.Arg>, rest: String) -> String:
  match a:
    case Nil{}:
      rest
    case Con{x, more}:
      w_arg(x, w_args.items(more, rest))

def w_args(+a: List<&2, Cl.Arg>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cl.Arg, a), w_args.items(a, rest))

def w_receipt(x: Cl.Receipt, rest: String) -> String:
  match x:
    case Cl.Renamed{a, b}:
      Wr.put_nat(0n, Wr.put_str(a, Wr.put_str(b, rest)))
    case Cl.Clashed{a, b}:
      Wr.put_nat(1n, Wr.put_str(a, Wr.put_str(b, rest)))
    case Cl.Filled{k}:
      Wr.put_nat(2n, Wr.put_str(k, rest))

def w_receipts.items(rs: List<&2, Cl.Receipt>, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case Con{x, more}:
      w_receipt(x, w_receipts.items(more, rest))

def w_receipts(+rs: List<&2, Cl.Receipt>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cl.Receipt, rs), w_receipts.items(rs, rest))

def w_lift(l: Cl.Lift, rest: String) -> String:
  match l:
    case Cl.Unknown{}:
      Wr.put_nat(0n, rest)
    case Cl.Current{}:
      Wr.put_nat(1n, rest)
    case Cl.Stranded{}:
      Wr.put_nat(2n, rest)
    case Cl.Lifted{r, a, rs}:
      Wr.put_nat(3n, Wr.put_str(r, w_args(a, w_receipts(rs, rest))))

# the spec's lifts of the calls by the shipped table, one after another
def w_lifts(cs: List<&2, Cl.Call>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case Con{c, more}:
      w_lift(Sp.lift_spec(Cl.table(), c), w_lifts(more, rest))

# the reply to a request: the count of the calls, then their lifts
def w_reply(+cs: List<&2, Cl.Call>) -> String:
  Wr.put_nat(List.length(&2, Cl.Call, cs), w_lifts(cs, ""))

# The reader (W3)
# ---------------

def r_call.keys(f: String, r: String, d: Wr.Dec<List<&2, String>>) -> Wr.Dec<Cl.Call>:
  match d:
    case Wr.Got{ks, s}:
      Wr.Got{Cl.Call{f, r, ks}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_call.rev(f: String, d: Wr.Dec<String>) -> Wr.Dec<Cl.Call>:
  match d:
    case Wr.Got{r, s}:
      r_call.keys(f, r, Wr.get_list(~String, ~Wr.get_str, s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_call.fam(d: Wr.Dec<String>) -> Wr.Dec<Cl.Call>:
  match d:
    case Wr.Got{f, s}:
      r_call.rev(f, Wr.get_str(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a call at the start of s, read with the wire's decoders
def r_call(s: String) -> Wr.Dec<Cl.Call>:
  r_call.fam(Wr.get_str(s))

def r_whole.end(b: Bool, cs: List<&2, Cl.Call>) -> Maybe<&2, List<&2, Cl.Call>>:
  match b:
    case True{}:
      Some{cs}
    case False{}:
      None{}

def r_whole(d: Wr.Dec<List<&2, Cl.Call>>) -> Maybe<&2, List<&2, Cl.Call>>:
  match d:
    case Wr.Got{cs, +s}:
      r_whole.end(Wr.end(s), cs)
    case Wr.Bad{}:
      None{}

# the request s spells whole, with nothing after it
def read(s: String) -> Maybe<&2, List<&2, Cl.Call>>:
  r_whole(Wr.get_list(~Cl.Call, ~r_call, s))

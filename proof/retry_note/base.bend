# eukhe: lemmas of the proofs of area retry_note

import Base
import ../../bend/retry_note.bend as Rn
import ../../bend/ffi_retry_note.bend as FRn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nat_too_long.bend as PWireNatTooLong
import ../base/logic/string.bend as LLogicString
import ../../laws/retry_note.bend as RetryNote

# ---- logic ----

# T at True, F at False
def rn.BD(b: Bool, T: Type, F: Type) -> Type:
  match b:
    case True{}:
      T
    case False{}:
      F

# False is not True: anything follows
def rn.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : rn.BD(_, G, Unit)
  Unit{}

# True is not False: anything follows
def rn.absurd_t(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : rn.BD(_, Unit, G)
  Unit{}

def rn.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      rn.absurd({False{} == True{} : Bool}, e)

def rn.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      rn.absurd({b == True{} : Bool}, e)

# ---- the text ----

def rn.append_nil(a: String) -> {String.append(a, "") == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      %rn.append_nil(t) : {SCon{c, String.append(t, "")} == SCon{c, _} : String}
      {==}

# the join of the shown calls r after a first text h is h, then the code's
# calls after the first
def rn.join_go(r: List<&2, Rn.Call>, +h: String) -> {String.join.go(RetryNote.shown_spec(r), h, "; ") == String.append(h, Rn.calls.rest(r)) : String}:
  match r:
    case Nil{}:
      Equal.sym(String, String.append(h, ""), h, rn.append_nil(h))
    case Rn.Call{ta, ar} <> +t:
      +cs = RetryNote.call_spec(Rn.Call{ta, ar})
      %Equal.sym(String, String.join.go(RetryNote.shown_spec(t), cs, "; "), String.append(cs, Rn.calls.rest(t)), rn.join_go(t, cs)) : {String.append(h, String.append("; ", _)) == String.append(h, String.append("; ", String.append(Rn.call(Rn.Call{ta, ar}), Rn.calls.rest(t)))) : String}
      {==}

# the code's calls are the shown calls joined by "; "
def rn.calls(cs: List<&2, Rn.Call>) -> {String.join(RetryNote.shown_spec(cs), "; ") == Rn.calls(cs) : String}:
  match cs:
    case Nil{}:
      {==}
    case Rn.Call{ta, ar} <> +t:
      rn.join_go(t, RetryNote.call_spec(Rn.Call{ta, ar}))

def rn.under(-s: String, -s1: String, -y: String, -f: String -> String, e: {s == f(s1) : String}, p: {s1 == y : String}) -> {s == f(y) : String}:
  %p : {s == f(_) : String}
  e

# ---- round trips ----

# a Nat that fits reads back
def rn.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

# a text that fits reads back
def rn.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

# a call whose texts fit reads back
def rn.rt_call(+ta: String, +ar: String, +rest: String, ht: {LawsBase.wire_fits(String.length(ta)) == True{} : Bool}, ha: {LawsBase.wire_fits(String.length(ar)) == True{} : Bool}) -> {FRn.get_call(RetryNote.spell_call(Rn.Call{ta, ar}, rest)) == Wr.Got{Rn.Call{ta, ar}, rest} : Wr.Dec<Rn.Call>}:
  %rn.str(ta, Wr.put_str(ar, rest), ht) : {FRn.get_call.tool(_) == Wr.Got{Rn.Call{ta, ar}, rest} : Wr.Dec<Rn.Call>}
  %rn.str(ar, rest, ha) : {FRn.get_call.args(ta, _) == Wr.Got{Rn.Call{ta, ar}, rest} : Wr.Dec<Rn.Call>}
  {==}

# the spelled calls xs, then rest
def rn.items(xs: List<&2, Rn.Call>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      RetryNote.spell_call(x, rn.items(t, rest))

# the list loop of the spec speller is the count and the items
def rn.put_go(xs: List<&2, Rn.Call>, -rest: String) -> {Wr.put_list.go(~Rn.Call, ~RetryNote.spell_call, xs, rest) == (List.length(&2, Rn.Call, xs), rn.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Rn.Call, ~RetryNote.spell_call, t, rest), (List.length(&2, Rn.Call, t), rn.items(t, rest)), rn.put_go(t, rest)) : {Wr.put_list.step(~Rn.Call, ~RetryNote.spell_call, x, _) == (1n+List.length(&2, Rn.Call, t), RetryNote.spell_call(x, rn.items(t, rest))) : Nat & String}
      {==}

# the spec spelling of a list of calls is its count, then its items
def rn.put_list(+xs: List<&2, Rn.Call>, -rest: String) -> {Wr.put_list(~Rn.Call, ~RetryNote.spell_call, xs, rest) == Wr.put_nat(List.length(&2, Rn.Call, xs), rn.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Rn.Call, ~RetryNote.spell_call, xs, rest), (List.length(&2, Rn.Call, xs), rn.items(xs, rest)), rn.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Rn.Call, xs), rn.items(xs, rest)) : String}
  {==}

# the tail of calls that fit fits
def rn.fit_tail(x: Rn.Call, -t: List<&2, Rn.Call>, h: {RetryNote.calls_fit(x <> t) == True{} : Bool}) -> {RetryNote.calls_fit(t) == True{} : Bool}:
  match x:
    case Rn.Call{+ta, +ar}:
      rn.and_r(Bool.and(LawsBase.wire_fits(String.length(ta)), LawsBase.wire_fits(String.length(ar))), RetryNote.calls_fit(t), h)

# the head of calls that fit reads back
def rn.rt_head(x: Rn.Call, -t: List<&2, Rn.Call>, +rest: String, h: {RetryNote.calls_fit(x <> t) == True{} : Bool}) -> {FRn.get_call(RetryNote.spell_call(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rn.Call>}:
  match x:
    case Rn.Call{+ta, +ar}:
      +hh = rn.and_l(Bool.and(LawsBase.wire_fits(String.length(ta)), LawsBase.wire_fits(String.length(ar))), RetryNote.calls_fit(t), h)
      rn.rt_call(ta, ar, rest, rn.and_l(LawsBase.wire_fits(String.length(ta)), LawsBase.wire_fits(String.length(ar)), hh), rn.and_r(LawsBase.wire_fits(String.length(ta)), LawsBase.wire_fits(String.length(ar)), hh))

# the decoder's loop reads back the items of calls that fit
def rn.loop(+t: List<&2, Rn.Call>, +x: Rn.Call, +rest: String, +hf: {RetryNote.calls_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Rn.Call, ~FRn.get_call, List.length(&2, Rn.Call, t), FRn.get_call(RetryNote.spell_call(x, rn.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Rn.Call>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Rn.Call>, FRn.get_call(RetryNote.spell_call(x, rest)), Wr.Got{x, rest}, rn.rt_head(x, Nil{}, rest, hf)) : {Wr.get_list.go(~Rn.Call, ~FRn.get_call, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Rn.Call>>}
      {==}
    case Con{+y, +u}:
      +r2 = RetryNote.spell_call(y, rn.items(u, rest))
      %Equal.sym(Wr.Dec<Rn.Call>, FRn.get_call(RetryNote.spell_call(x, r2)), Wr.Got{x, r2}, rn.rt_head(x, y <> u, r2, hf)) : {Wr.get_list.go(~Rn.Call, ~FRn.get_call, 1n+List.length(&2, Rn.Call, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Rn.Call>>}
      %Equal.sym(Wr.Dec<List<&2, Rn.Call>>, Wr.get_list.go(~Rn.Call, ~FRn.get_call, List.length(&2, Rn.Call, u), FRn.get_call(r2)), Wr.Got{y <> u, rest}, rn.loop(u, y, rest, rn.fit_tail(x, y <> u, hf))) : {Wr.get_list.cons(Rn.Call, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Rn.Call>>}
      {==}

# a list of calls that fits reads back
def rn.list_rt(+xs: List<&2, Rn.Call>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, Rn.Call, xs)) == True{} : Bool}, hi: {RetryNote.calls_fit(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~Rn.Call, ~FRn.get_call, Wr.put_list(~Rn.Call, ~RetryNote.spell_call, xs, rest)) : Wr.Dec<List<&2, Rn.Call>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, hl)) : {Wr.Got{Nil{}, rest} == Wr.get_list.start(~Rn.Call, ~FRn.get_call, _) : Wr.Dec<List<&2, Rn.Call>>}
      {==}
    case Con{+x, +t}:
      +items = rn.items(x <> t, rest)
      %Equal.sym(String, Wr.put_list(~Rn.Call, ~RetryNote.spell_call, x <> t, rest), Wr.put_nat(List.length(&2, Rn.Call, x <> t), items), rn.put_list(x <> t, rest)) : {Wr.Got{x <> t, rest} == Wr.get_list(~Rn.Call, ~FRn.get_call, _) : Wr.Dec<List<&2, Rn.Call>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Rn.Call, x <> t), items)), Wr.Got{List.length(&2, Rn.Call, x <> t), items}, Wire.wire_nat_round_trip(List.length(&2, Rn.Call, x <> t), items, hl)) : {Wr.Got{x <> t, rest} == Wr.get_list.start(~Rn.Call, ~FRn.get_call, _) : Wr.Dec<List<&2, Rn.Call>>}
      Equal.sym(Wr.Dec<List<&2, Rn.Call>>, Wr.get_list.go(~Rn.Call, ~FRn.get_call, List.length(&2, Rn.Call, t), FRn.get_call(RetryNote.spell_call(x, rn.items(t, rest)))), Wr.Got{x <> t, rest}, rn.loop(t, x, rest, hi))

# three Nats that fit read back
def rn.rt_three(+a: Nat, +b: Nat, +c: Nat, +rest: String, ha: {LawsBase.wire_fits(a) == True{} : Bool}, hb: {LawsBase.wire_fits(b) == True{} : Bool}, hc: {LawsBase.wire_fits(c) == True{} : Bool}) -> {Wr.Got{FRn.Three{a, b, c}, rest} == FRn.get_three(Wr.get_nat(Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, rest))))) : Wr.Dec<FRn.Three>}:
  %rn.nat(a, Wr.put_nat(b, Wr.put_nat(c, rest)), ha) : {Wr.Got{FRn.Three{a, b, c}, rest} == FRn.get_three(_) : Wr.Dec<FRn.Three>}
  %rn.nat(b, Wr.put_nat(c, rest), hb) : {Wr.Got{FRn.Three{a, b, c}, rest} == FRn.get_three.b(a, _) : Wr.Dec<FRn.Three>}
  %rn.nat(c, rest, hc) : {Wr.Got{FRn.Three{a, b, c}, rest} == FRn.get_three.c(a, b, _) : Wr.Dec<FRn.Three>}
  {==}

# a cause whose numbers, texts and count fit reads back
def rn.rt_cause(+c: Rn.Cause, +rest: String, +h: {RetryNote.cause_fits(c) == True{} : Bool}) -> {FRn.get_cause(Wr.get_nat(RetryNote.spell_cause(c, rest))) == Wr.Got{c, rest} : Wr.Dec<Rn.Cause>}:
  match c:
    case Rn.Repeated{+p, +l}:
      %rn.nat(0n, Wr.put_nat(p, Wr.put_str(l, rest)), {==}) : {FRn.get_cause(_) == Wr.Got{Rn.Repeated{p, l}, rest} : Wr.Dec<Rn.Cause>}
      %rn.nat(p, Wr.put_str(l, rest), rn.and_l(LawsBase.wire_fits(p), LawsBase.wire_fits(String.length(l)), h)) : {FRn.get_repeated(_) == Wr.Got{Rn.Repeated{p, l}, rest} : Wr.Dec<Rn.Cause>}
      %rn.str(l, rest, rn.and_r(LawsBase.wire_fits(p), LawsBase.wire_fits(String.length(l)), h)) : {FRn.get_repeated.line(p, _) == Wr.Got{Rn.Repeated{p, l}, rest} : Wr.Dec<Rn.Cause>}
      {==}
    case Rn.NoAnswer{}:
      %rn.nat(1n, rest, {==}) : {FRn.get_cause(_) == Wr.Got{Rn.NoAnswer{}, rest} : Wr.Dec<Rn.Cause>}
      {==}
    case Rn.Length{+t, +r, +k}:
      +hrk = rn.and_r(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k)), h)
      %rn.nat(2n, Wr.put_nat(t, Wr.put_nat(r, Wr.put_nat(k, rest))), {==}) : {FRn.get_cause(_) == Wr.Got{Rn.Length{t, r, k}, rest} : Wr.Dec<Rn.Cause>}
      %rn.rt_three(t, r, k, rest, rn.and_l(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k)), h), rn.and_l(LawsBase.wire_fits(r), LawsBase.wire_fits(k), hrk), rn.and_r(LawsBase.wire_fits(r), LawsBase.wire_fits(k), hrk)) : {FRn.get_length(_) == Wr.Got{Rn.Length{t, r, k}, rest} : Wr.Dec<Rn.Cause>}
      {==}
    case Rn.Leaked{+m, +why, +r, +k}:
      +hs = rn.and_l(Bool.and(LawsBase.wire_fits(String.length(m)), LawsBase.wire_fits(String.length(why))), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k)), h)
      +hn = rn.and_r(Bool.and(LawsBase.wire_fits(String.length(m)), LawsBase.wire_fits(String.length(why))), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k)), h)
      %rn.nat(3n, Wr.put_str(m, Wr.put_str(why, Wr.put_nat(r, Wr.put_nat(k, rest)))), {==}) : {FRn.get_cause(_) == Wr.Got{Rn.Leaked{m, why, r, k}, rest} : Wr.Dec<Rn.Cause>}
      %rn.str(m, Wr.put_str(why, Wr.put_nat(r, Wr.put_nat(k, rest))), rn.and_l(LawsBase.wire_fits(String.length(m)), LawsBase.wire_fits(String.length(why)), hs)) : {FRn.get_leaked(_) == Wr.Got{Rn.Leaked{m, why, r, k}, rest} : Wr.Dec<Rn.Cause>}
      %rn.str(why, Wr.put_nat(r, Wr.put_nat(k, rest)), rn.and_r(LawsBase.wire_fits(String.length(m)), LawsBase.wire_fits(String.length(why)), hs)) : {FRn.get_leaked.reason(m, _) == Wr.Got{Rn.Leaked{m, why, r, k}, rest} : Wr.Dec<Rn.Cause>}
      %rn.nat(r, Wr.put_nat(k, rest), rn.and_l(LawsBase.wire_fits(r), LawsBase.wire_fits(k), hn)) : {FRn.get_leaked.row(m, why, _) == Wr.Got{Rn.Leaked{m, why, r, k}, rest} : Wr.Dec<Rn.Cause>}
      %rn.nat(k, rest, rn.and_r(LawsBase.wire_fits(r), LawsBase.wire_fits(k), hn)) : {FRn.get_leaked.cap(m, why, r, _) == Wr.Got{Rn.Leaked{m, why, r, k}, rest} : Wr.Dec<Rn.Cause>}
      {==}
    case Rn.Redirect{+cs, +n, +r, +k}:
      +hl = rn.and_l(Bool.and(LawsBase.wire_fits(List.length(&2, Rn.Call, cs)), RetryNote.calls_fit(cs)), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k))), h)
      +hn = rn.and_r(Bool.and(LawsBase.wire_fits(List.length(&2, Rn.Call, cs)), RetryNote.calls_fit(cs)), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k))), h)
      +hrk = rn.and_r(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k)), hn)
      +tail = Wr.put_nat(n, Wr.put_nat(r, Wr.put_nat(k, rest)))
      %rn.nat(4n, Wr.put_list(~Rn.Call, ~RetryNote.spell_call, cs, tail), {==}) : {FRn.get_cause(_) == Wr.Got{Rn.Redirect{cs, n, r, k}, rest} : Wr.Dec<Rn.Cause>}
      %rn.list_rt(cs, tail, rn.and_l(LawsBase.wire_fits(List.length(&2, Rn.Call, cs)), RetryNote.calls_fit(cs), hl), rn.and_r(LawsBase.wire_fits(List.length(&2, Rn.Call, cs)), RetryNote.calls_fit(cs), hl)) : {FRn.get_redirect(_) == Wr.Got{Rn.Redirect{cs, n, r, k}, rest} : Wr.Dec<Rn.Cause>}
      %rn.rt_three(n, r, k, rest, rn.and_l(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k)), hn), rn.and_l(LawsBase.wire_fits(r), LawsBase.wire_fits(k), hrk), rn.and_r(LawsBase.wire_fits(r), LawsBase.wire_fits(k), hrk)) : {FRn.get_redirect.counts(cs, _) == Wr.Got{Rn.Redirect{cs, n, r, k}, rest} : Wr.Dec<Rn.Cause>}
      {==}
    case Rn.Stalled{+ms}:
      %rn.nat(5n, Wr.put_nat(ms, rest), {==}) : {FRn.get_cause(_) == Wr.Got{Rn.Stalled{ms}, rest} : Wr.Dec<Rn.Cause>}
      %rn.nat(ms, rest, h) : {FRn.get_stalled(_) == Wr.Got{Rn.Stalled{ms}, rest} : Wr.Dec<Rn.Cause>}
      {==}

# a request that fits reads back: the entry is at its last step
def rn.reads(+q: FRn.Req, +rest: String, +h: {RetryNote.req_fits(q) == True{} : Bool}) -> {FRn.ffi(RetryNote.spell_req(q, rest)) == FRn.ffi.done(q, Wr.end(rest)) : String}:
  match q:
    case FRn.Req{+a, +c}:
      %rn.nat(a, RetryNote.spell_cause(c, rest), rn.and_l(LawsBase.wire_fits(a), RetryNote.cause_fits(c), h)) : {FRn.ffi.got(FRn.get_req(_)) == FRn.ffi.done(FRn.Req{a, c}, Wr.end(rest)) : String}
      %Equal.sym(Wr.Dec<Rn.Cause>, FRn.get_cause(Wr.get_nat(RetryNote.spell_cause(c, rest))), Wr.Got{c, rest}, rn.rt_cause(c, rest, rn.and_r(LawsBase.wire_fits(a), RetryNote.cause_fits(c), h))) : {FRn.ffi.got(FRn.get_req.cause(a, _)) == FRn.ffi.done(FRn.Req{a, c}, Wr.end(rest)) : String}
      {==}

# ---- exactness: what each decoder reads is spelled ----

# what a Nat decoder's answer says about its input s
def rn.PN(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String}
    case Wr.Bad{}:
      Unit

def rn.pn_go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rn.PN(s, d):
  match d:
    case Wr.Got{+n, +r}:
      Wire.wire_nat_exact(s, n, r, ed)
    case Wr.Bad{}:
      Unit{}

def rn.pn(+s: String) -> rn.PN(s, Wr.get_nat(s)):
  rn.pn_go(s, Wr.get_nat(s), {==})

# what a text decoder's answer says about its input s
def rn.PS(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_str(a, r) : String}
    case Wr.Bad{}:
      Unit

def rn.ps_go(+s: String, d: Wr.Dec<String>, +ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> rn.PS(s, d):
  match d:
    case Wr.Got{+a, +r}:
      Wire.wire_str_exact(s, a, r, ed)
    case Wr.Bad{}:
      Unit{}

def rn.ps(+s: String) -> rn.PS(s, Wr.get_str(s)):
  rn.ps_go(s, Wr.get_str(s), {==})

# what a call decoder's answer says about its input s
def rn.PC(s: String, d: Wr.Dec<Rn.Call>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == RetryNote.spell_call(c, r) : String}
    case Wr.Bad{}:
      Unit

def rn.pc_args(-s: String, -ta: String, -s1: String, e1: {s == Wr.put_str(ta, s1) : String}, d: Wr.Dec<String>, p2: rn.PS(s1, d)) -> rn.PC(s, FRn.get_call.args(ta, d)):
  match d:
    case Wr.Got{ar, r}:
      rn.under(s, s1, Wr.put_str(ar, r), z => Wr.put_str(ta, z), e1, p2)
    case Wr.Bad{}:
      Unit{}

def rn.pc_tool(-s: String, d: Wr.Dec<String>, p1: rn.PS(s, d)) -> rn.PC(s, FRn.get_call.tool(d)):
  match d:
    case Wr.Got{+ta, +s1}:
      rn.pc_args(s, ta, s1, p1, Wr.get_str(s1), rn.ps(s1))
    case Wr.Bad{}:
      Unit{}

def rn.pc(+s: String) -> rn.PC(s, FRn.get_call(s)):
  rn.pc_tool(s, Wr.get_str(s), rn.ps(s))

# what the item loop's answer says about its input s (m + 1 items)
def rn.PLL(s: String, m: Nat, d: Wr.Dec<List<&2, Rn.Call>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == rn.items(xs, r) : String} & {List.length(&2, Rn.Call, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

# one more spelled call before the rest of the loop
def rn.ll_step(-s: String, +x: Rn.Call, -s3: String, -k: Nat, d: Wr.Dec<List<&2, Rn.Call>>, ih: rn.PLL(s3, k, d), px: rn.PC(s, Wr.Got{x, s3})) -> rn.PLL(s, 1n+k, Wr.get_list.cons(Rn.Call, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (rn.under(s, s3, rn.items(ys, r), z => RetryNote.spell_call(x, z), px, e1), Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Rn.Call, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled calls
def rn.ll_loop(m: Nat, cur: Wr.Dec<Rn.Call>, +s: String, pc: rn.PC(s, cur)) -> rn.PLL(s, m, Wr.get_list.go(~Rn.Call, ~FRn.get_call, m, cur)):
  match m cur:
    case 0n Wr.Got{x, s3}:
      (pc, {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      rn.ll_step(s, x, s3, k, Wr.get_list.go(~Rn.Call, ~FRn.get_call, k, FRn.get_call(s3)), rn.ll_loop(k, FRn.get_call(s3), s3, rn.pc(s3)), pc)
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list-of-calls decoder's answer says about its input s
def rn.PLS(s: String, d: Wr.Dec<List<&2, Rn.Call>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~Rn.Call, ~RetryNote.spell_call, xs, r) : String}
    case Wr.Bad{}:
      Unit

# the count spelled before the items is the list's length
def rn.ll_eq(-s: String, -s2: String, -m: Nat, +xs: List<&2, Rn.Call>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == rn.items(xs, r) : String}, e2: {List.length(&2, Rn.Call, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Rn.Call, ~RetryNote.spell_call, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Rn.Call, ~RetryNote.spell_call, xs, r), Wr.put_nat(List.length(&2, Rn.Call, xs), rn.items(xs, r)), rn.put_list(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Rn.Call, xs), 1n+m, e2) : {s == Wr.put_nat(_, rn.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def rn.ll_conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, d: Wr.Dec<List<&2, Rn.Call>>, pl: rn.PLL(s2, m, d)) -> rn.PLS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = pl
      rn.ll_eq(s, s2, m, xs, r, en, e1, e2)
    case Wr.Bad{}:
      Unit{}

# the count 0 is the empty list; else the item loop runs
def rn.ll_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}) -> rn.PLS(s, Wr.get_list.start(~Rn.Call, ~FRn.get_call, Wr.Got{n, s2})):
  match n:
    case 0n:
      en
    case 1n++m:
      rn.ll_conv(s, s2, m, en, Wr.get_list.go(~Rn.Call, ~FRn.get_call, m, FRn.get_call(s2)), rn.ll_loop(m, FRn.get_call(s2), s2, rn.pc(s2)))

def rn.ll_top(+s: String, d: Wr.Dec<Nat>, pn: rn.PN(s, d)) -> rn.PLS(s, Wr.get_list.start(~Rn.Call, ~FRn.get_call, d)):
  match d:
    case Wr.Got{+n, +s2}:
      rn.ll_nat(s, n, s2, pn)
    case Wr.Bad{}:
      Unit{}

def rn.pls(+s: String) -> rn.PLS(s, Wr.get_list(~Rn.Call, ~FRn.get_call, s)):
  rn.ll_top(s, Wr.get_nat(s), rn.pn(s))

# what the three-Nat decoder's answer says about its input s
def rn.P3(s: String, d: Wr.Dec<FRn.Three>) -> Type:
  match d:
    case Wr.Got{x, r}:
      match x:
        case FRn.Three{a, b, c}:
          {s == Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, r))) : String}
    case Wr.Bad{}:
      Unit

def rn.p3_c(-s: String, -a: Nat, -b: Nat, -s2: String, e: {s == Wr.put_nat(a, Wr.put_nat(b, s2)) : String}, d: Wr.Dec<Nat>, pn: rn.PN(s2, d)) -> rn.P3(s, FRn.get_three.c(a, b, d)):
  match d:
    case Wr.Got{c, r}:
      rn.under(s, s2, Wr.put_nat(c, r), z => Wr.put_nat(a, Wr.put_nat(b, z)), e, pn)
    case Wr.Bad{}:
      Unit{}

def rn.p3_b(-s: String, -a: Nat, -s1: String, e: {s == Wr.put_nat(a, s1) : String}, d: Wr.Dec<Nat>, pn: rn.PN(s1, d)) -> rn.P3(s, FRn.get_three.b(a, d)):
  match d:
    case Wr.Got{+b, +s2}:
      rn.p3_c(s, a, b, s2, rn.under(s, s1, Wr.put_nat(b, s2), z => Wr.put_nat(a, z), e, pn), Wr.get_nat(s2), rn.pn(s2))
    case Wr.Bad{}:
      Unit{}

def rn.p3_a(+s: String, d: Wr.Dec<Nat>, pn: rn.PN(s, d)) -> rn.P3(s, FRn.get_three(d)):
  match d:
    case Wr.Got{+a, +s1}:
      rn.p3_b(s, a, s1, pn, Wr.get_nat(s1), rn.pn(s1))
    case Wr.Bad{}:
      Unit{}

def rn.p3(+s: String) -> rn.P3(s, FRn.get_three(Wr.get_nat(s))):
  rn.p3_a(s, Wr.get_nat(s), rn.pn(s))

# what a cause decoder's answer says about its input s
def rn.PCa(s: String, d: Wr.Dec<Rn.Cause>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == RetryNote.spell_cause(c, r) : String}
    case Wr.Bad{}:
      Unit

def rn.pca_rep_line(-s: String, -p: Nat, -s2: String, e: {s == Wr.put_nat(0n, Wr.put_nat(p, s2)) : String}, d: Wr.Dec<String>, ps: rn.PS(s2, d)) -> rn.PCa(s, FRn.get_repeated.line(p, d)):
  match d:
    case Wr.Got{l, r}:
      rn.under(s, s2, Wr.put_str(l, r), z => Wr.put_nat(0n, Wr.put_nat(p, z)), e, ps)
    case Wr.Bad{}:
      Unit{}

def rn.pca_rep(-s: String, -s1: String, e0: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, pn: rn.PN(s1, d)) -> rn.PCa(s, FRn.get_repeated(d)):
  match d:
    case Wr.Got{+p, +s2}:
      rn.pca_rep_line(s, p, s2, rn.under(s, s1, Wr.put_nat(p, s2), z => Wr.put_nat(0n, z), e0, pn), Wr.get_str(s2), rn.ps(s2))
    case Wr.Bad{}:
      Unit{}

def rn.pca_len(-s: String, -s1: String, e0: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<FRn.Three>, p3: rn.P3(s1, d)) -> rn.PCa(s, FRn.get_length(d)):
  match d:
    case Wr.Got{x, r}:
      match x:
        case FRn.Three{t, w, k}:
          rn.under(s, s1, Wr.put_nat(t, Wr.put_nat(w, Wr.put_nat(k, r))), z => Wr.put_nat(2n, z), e0, p3)
    case Wr.Bad{}:
      Unit{}

def rn.pca_lk_cap(-s: String, -m: String, -why: String, -w: Nat, -s4: String, e: {s == Wr.put_nat(3n, Wr.put_str(m, Wr.put_str(why, Wr.put_nat(w, s4)))) : String}, d: Wr.Dec<Nat>, pn: rn.PN(s4, d)) -> rn.PCa(s, FRn.get_leaked.cap(m, why, w, d)):
  match d:
    case Wr.Got{k, r}:
      rn.under(s, s4, Wr.put_nat(k, r), z => Wr.put_nat(3n, Wr.put_str(m, Wr.put_str(why, Wr.put_nat(w, z)))), e, pn)
    case Wr.Bad{}:
      Unit{}

def rn.pca_lk_row(-s: String, -m: String, -why: String, -s3: String, e: {s == Wr.put_nat(3n, Wr.put_str(m, Wr.put_str(why, s3))) : String}, d: Wr.Dec<Nat>, pn: rn.PN(s3, d)) -> rn.PCa(s, FRn.get_leaked.row(m, why, d)):
  match d:
    case Wr.Got{+w, +s4}:
      rn.pca_lk_cap(s, m, why, w, s4, rn.under(s, s3, Wr.put_nat(w, s4), z => Wr.put_nat(3n, Wr.put_str(m, Wr.put_str(why, z))), e, pn), Wr.get_nat(s4), rn.pn(s4))
    case Wr.Bad{}:
      Unit{}

def rn.pca_lk_reason(-s: String, -m: String, -s2: String, e: {s == Wr.put_nat(3n, Wr.put_str(m, s2)) : String}, d: Wr.Dec<String>, ps: rn.PS(s2, d)) -> rn.PCa(s, FRn.get_leaked.reason(m, d)):
  match d:
    case Wr.Got{+why, +s3}:
      rn.pca_lk_row(s, m, why, s3, rn.under(s, s2, Wr.put_str(why, s3), z => Wr.put_nat(3n, Wr.put_str(m, z)), e, ps), Wr.get_nat(s3), rn.pn(s3))
    case Wr.Bad{}:
      Unit{}

def rn.pca_lk(-s: String, -s1: String, e0: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<String>, ps: rn.PS(s1, d)) -> rn.PCa(s, FRn.get_leaked(d)):
  match d:
    case Wr.Got{+m, +s2}:
      rn.pca_lk_reason(s, m, s2, rn.under(s, s1, Wr.put_str(m, s2), z => Wr.put_nat(3n, z), e0, ps), Wr.get_str(s2), rn.ps(s2))
    case Wr.Bad{}:
      Unit{}

def rn.pca_rd_counts(-s: String, -cs: List<&2, Rn.Call>, -s2: String, e: {s == Wr.put_nat(4n, Wr.put_list(~Rn.Call, ~RetryNote.spell_call, cs, s2)) : String}, d: Wr.Dec<FRn.Three>, p3: rn.P3(s2, d)) -> rn.PCa(s, FRn.get_redirect.counts(cs, d)):
  match d:
    case Wr.Got{x, r}:
      match x:
        case FRn.Three{n, w, k}:
          rn.under(s, s2, Wr.put_nat(n, Wr.put_nat(w, Wr.put_nat(k, r))), z => Wr.put_nat(4n, Wr.put_list(~Rn.Call, ~RetryNote.spell_call, cs, z)), e, p3)
    case Wr.Bad{}:
      Unit{}

def rn.pca_rd(-s: String, -s1: String, e0: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<List<&2, Rn.Call>>, pl: rn.PLS(s1, d)) -> rn.PCa(s, FRn.get_redirect(d)):
  match d:
    case Wr.Got{+cs, +s2}:
      rn.pca_rd_counts(s, cs, s2, rn.under(s, s1, Wr.put_list(~Rn.Call, ~RetryNote.spell_call, cs, s2), z => Wr.put_nat(4n, z), e0, pl), FRn.get_three(Wr.get_nat(s2)), rn.p3(s2))
    case Wr.Bad{}:
      Unit{}

def rn.pca_st(-s: String, -s1: String, e0: {s == Wr.put_nat(5n, s1) : String}, d: Wr.Dec<Nat>, pn: rn.PN(s1, d)) -> rn.PCa(s, FRn.get_stalled(d)):
  match d:
    case Wr.Got{ms, r}:
      rn.under(s, s1, Wr.put_nat(ms, r), z => Wr.put_nat(5n, z), e0, pn)
    case Wr.Bad{}:
      Unit{}

def rn.pca_tag(+s: String, d: Wr.Dec<Nat>, pn: rn.PN(s, d)) -> rn.PCa(s, FRn.get_cause(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          rn.pca_rep(s, s1, pn, Wr.get_nat(s1), rn.pn(s1))
        case 1n:
          pn
        case 2n:
          rn.pca_len(s, s1, pn, FRn.get_three(Wr.get_nat(s1)), rn.p3(s1))
        case 3n:
          rn.pca_lk(s, s1, pn, Wr.get_str(s1), rn.ps(s1))
        case 4n:
          rn.pca_rd(s, s1, pn, Wr.get_list(~Rn.Call, ~FRn.get_call, s1), rn.pls(s1))
        case 5n:
          rn.pca_st(s, s1, pn, Wr.get_nat(s1), rn.pn(s1))
        case 6n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rn.pca(+s: String) -> rn.PCa(s, FRn.get_cause(Wr.get_nat(s))):
  rn.pca_tag(s, Wr.get_nat(s), rn.pn(s))

# what the request decoder's answer says about its input s
def rn.PR(s: String, d: Wr.Dec<FRn.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == RetryNote.spell_req(q, r) : String}
    case Wr.Bad{}:
      Unit

def rn.pr_cause(-s: String, -a: Nat, -s1: String, e: {s == Wr.put_nat(a, s1) : String}, d: Wr.Dec<Rn.Cause>, pc: rn.PCa(s1, d)) -> rn.PR(s, FRn.get_req.cause(a, d)):
  match d:
    case Wr.Got{c, r}:
      rn.under(s, s1, RetryNote.spell_cause(c, r), z => Wr.put_nat(a, z), e, pc)
    case Wr.Bad{}:
      Unit{}

def rn.pr_top(+s: String, d: Wr.Dec<Nat>, pn: rn.PN(s, d)) -> rn.PR(s, FRn.get_req(d)):
  match d:
    case Wr.Got{+a, +s1}:
      rn.pr_cause(s, a, s1, pn, FRn.get_cause(Wr.get_nat(s1)), rn.pca(s1))
    case Wr.Bad{}:
      Unit{}

# every request the decoder reads is spelled, and so is the input after it
def rn.pr(+s: String) -> rn.PR(s, FRn.get_req(Wr.get_nat(s))):
  rn.pr_top(s, Wr.get_nat(s), rn.pn(s))

# ---- replies ----

def rn.sfin(p: Nat & String, rest: String) -> {LawsBase.wire_opens_err(Wr.put_str.fin(p, rest)) == False{} : Bool}:
  match p:
    case (n, b):
      Wire.wire_nat_not_err(n, String.reverse.go(b, rest))

# a spelled text opens with its length, never with 'E'
def rn.str_not_err(a: String, rest: String) -> {LawsBase.wire_opens_err(Wr.put_str(a, rest)) == False{} : Bool}:
  rn.sfin(Wr.put_str.go(a, SNil{}, 0n), rest)

# a spelled text is no error form
def rn.put_not_err(-G: Type, +x: String, -t: String, e: {Wr.put_str(x, "") == Wr.err(t) : String}) -> G:
  rn.absurd(G, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(Wr.put_str(x, "")), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(Wr.put_str(x, "")), False{}, rn.str_not_err(x, "")), Equal.cong(String, Bool, z => LawsBase.wire_opens_err(z), Wr.put_str(x, ""), Wr.err(t), e)))

# ---- fits: every number, text and count the request decoder reads fits the wire ----

# both sides of an and hold, so it does
def rn.and2(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# Unit at Bad, G at Got
def rn.dec_if(d: Wr.Dec<String>, G: Type) -> Type:
  match d:
    case Wr.Got{a, r}:
      G
    case Wr.Bad{}:
      Unit

def rn.got_bad(-a: String, -r: String, -G: Type, e: {Wr.Bad{} == Wr.Got{a, r} : Wr.Dec<String>}) -> G:
  %e : rn.dec_if(_, G)
  Unit{}

# ---- Nat ----

def rn.FN(d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rn.fn_go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rn.FN(d):
  match d:
    case Wr.Got{+n, +r}:
      Wire.wire_nat_decoded_fits(s, n, r, ed)
    case Wr.Bad{}:
      Unit{}

def rn.fn(+s: String) -> rn.FN(Wr.get_nat(s)):
  rn.fn_go(s, Wr.get_nat(s), {==})

# ---- String ----

# a decoded text's length was read as a Nat: one past the wire makes the
# read Bad (wire_nat_too_long)
def rn.str_fits_b(b: Bool, +s: String, +a: String, +r: String, eb: {LawsBase.wire_fits(String.length(a)) == b : Bool}, es: {s == Wr.put_nat(String.length(a), LLogicString.wr_app(a, r)) : String}, ed: {Wr.get_str(s) == Wr.Got{a, r} : Wr.Dec<String>}) -> {LawsBase.wire_fits(String.length(a)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +p = Wr.put_nat(String.length(a), LLogicString.wr_app(a, r))
      +too = Wire.wire_nat_too_long(String.length(a), LLogicString.wr_app(a, r), eb)
      +c1 = Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), s, p, es)
      +c2 = Equal.cong(Wr.Dec<Nat>, Wr.Dec<String>, z => Wr.get_str.go(z), Wr.get_nat(p), Wr.Bad{}, too)
      +e1 = Equal.trans(Wr.Dec<String>, Wr.Bad{}, Wr.get_str(p), Wr.get_str(s), Equal.sym(Wr.Dec<String>, Wr.get_str(p), Wr.Bad{}, c2), Equal.sym(Wr.Dec<String>, Wr.get_str(s), Wr.get_str(p), c1))
      rn.got_bad(a, r, {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, Equal.trans(Wr.Dec<String>, Wr.Bad{}, Wr.get_str(s), Wr.Got{a, r}, e1, ed))

def rn.str_fits(+s: String, +a: String, +r: String, +ed: {Wr.get_str(s) == Wr.Got{a, r} : Wr.Dec<String>}) -> {LawsBase.wire_fits(String.length(a)) == True{} : Bool}:
  rn.str_fits_b(LawsBase.wire_fits(String.length(a)), s, a, r, {==}, Equal.trans(String, s, Wr.put_str(a, r), Wr.put_nat(String.length(a), LLogicString.wr_app(a, r)), Wire.wire_str_exact(s, a, r, ed), LWire.wr_put_str(a, r)), ed)

def rn.FS(d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rn.fs_go(+s: String, d: Wr.Dec<String>, +ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> rn.FS(d):
  match d:
    case Wr.Got{+a, +r}:
      rn.str_fits(s, a, r, ed)
    case Wr.Bad{}:
      Unit{}

def rn.fs(+s: String) -> rn.FS(Wr.get_str(s)):
  rn.fs_go(s, Wr.get_str(s), {==})

# ---- Call ----

def rn.FC(d: Wr.Dec<Rn.Call>) -> Type:
  match d:
    case Wr.Got{c, r}:
      match c:
        case Rn.Call{+t, +a}:
          {Bool.and(LawsBase.wire_fits(String.length(t)), LawsBase.wire_fits(String.length(a))) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rn.fc_args(-t: String, ft: {LawsBase.wire_fits(String.length(t)) == True{} : Bool}, d: Wr.Dec<String>, fa: rn.FS(d)) -> rn.FC(FRn.get_call.args(t, d)):
  match d:
    case Wr.Got{+a, r}:
      rn.and2(LawsBase.wire_fits(String.length(t)), LawsBase.wire_fits(String.length(a)), ft, fa)
    case Wr.Bad{}:
      Unit{}

def rn.fc_tool(d: Wr.Dec<String>, ft: rn.FS(d)) -> rn.FC(FRn.get_call.tool(d)):
  match d:
    case Wr.Got{+t, +s1}:
      rn.fc_args(t, ft, Wr.get_str(s1), rn.fs(s1))
    case Wr.Bad{}:
      Unit{}

def rn.fc(+s: String) -> rn.FC(FRn.get_call(s)):
  rn.fc_tool(Wr.get_str(s), rn.fs(s))

# ---- List<Call> ----

# the item loop's answer (m + 1 items): the calls fit and there are m + 1
def rn.FLL(m: Nat, d: Wr.Dec<List<&2, Rn.Call>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {RetryNote.calls_fit(xs) == True{} : Bool} & {List.length(&2, Rn.Call, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def rn.fl_step(x: Rn.Call, -s3: String, -k: Nat, d: Wr.Dec<List<&2, Rn.Call>>, ih: rn.FLL(k, d), fx: rn.FC(Wr.Got{x, s3})) -> rn.FLL(1n+k, Wr.get_list.cons(Rn.Call, x, d)):
  match x:
    case Rn.Call{+t, +a}:
      match d:
        case Wr.Got{+ys, r}:
          (e1, e2) = ih
          (rn.and2(Bool.and(LawsBase.wire_fits(String.length(t)), LawsBase.wire_fits(String.length(a))), RetryNote.calls_fit(ys), fx, e1), Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Rn.Call, ys), 1n+k, e2))
        case Wr.Bad{}:
          Unit{}

def rn.fl_loop(m: Nat, cur: Wr.Dec<Rn.Call>, fc: rn.FC(cur)) -> rn.FLL(m, Wr.get_list.go(~Rn.Call, ~FRn.get_call, m, cur)):
  match m cur:
    case 0n Wr.Got{x, s3}:
      match x:
        case Rn.Call{+t, +a}:
          (rn.and2(Bool.and(LawsBase.wire_fits(String.length(t)), LawsBase.wire_fits(String.length(a))), True{}, fc, {==}), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      rn.fl_step(x, s3, k, Wr.get_list.go(~Rn.Call, ~FRn.get_call, k, FRn.get_call(s3)), rn.fl_loop(k, FRn.get_call(s3), rn.fc(s3)), fc)
    case 1n++k Wr.Bad{}:
      Unit{}

def rn.FLS(d: Wr.Dec<List<&2, Rn.Call>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {Bool.and(LawsBase.wire_fits(List.length(&2, Rn.Call, xs)), RetryNote.calls_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rn.fl_conv(-m: Nat, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Rn.Call>>, fl: rn.FLL(m, d)) -> rn.FLS(d):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = fl
      rn.and2(LawsBase.wire_fits(List.length(&2, Rn.Call, xs)), RetryNote.calls_fit(xs), Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Rn.Call, xs)), LawsBase.wire_fits(1n+m), True{}, Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, Rn.Call, xs), 1n+m, e2), fn), e1)
    case Wr.Bad{}:
      Unit{}

def rn.fl_nat(n: Nat, +s2: String, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> rn.FLS(Wr.get_list.start(~Rn.Call, ~FRn.get_call, Wr.Got{n, s2})):
  match n:
    case 0n:
      {==}
    case 1n++m:
      rn.fl_conv(m, fn, Wr.get_list.go(~Rn.Call, ~FRn.get_call, m, FRn.get_call(s2)), rn.fl_loop(m, FRn.get_call(s2), rn.fc(s2)))

def rn.fl_top(d: Wr.Dec<Nat>, fn: rn.FN(d)) -> rn.FLS(Wr.get_list.start(~Rn.Call, ~FRn.get_call, d)):
  match d:
    case Wr.Got{+n, +s2}:
      rn.fl_nat(n, s2, fn)
    case Wr.Bad{}:
      Unit{}

def rn.fls(+s: String) -> rn.FLS(Wr.get_list(~Rn.Call, ~FRn.get_call, s)):
  rn.fl_top(Wr.get_nat(s), rn.fn(s))

# ---- three Nats ----

def rn.F3(d: Wr.Dec<FRn.Three>) -> Type:
  match d:
    case Wr.Got{x, r}:
      match x:
        case FRn.Three{+a, +b, +c}:
          {Bool.and(LawsBase.wire_fits(a), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(c))) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rn.f3_c(-a: Nat, -b: Nat, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, d: Wr.Dec<Nat>, fc: rn.FN(d)) -> rn.F3(FRn.get_three.c(a, b, d)):
  match d:
    case Wr.Got{+c, r}:
      rn.and2(LawsBase.wire_fits(a), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(c)), fa, rn.and2(LawsBase.wire_fits(b), LawsBase.wire_fits(c), fb, fc))
    case Wr.Bad{}:
      Unit{}

def rn.f3_b(-a: Nat, fa: {LawsBase.wire_fits(a) == True{} : Bool}, d: Wr.Dec<Nat>, fb: rn.FN(d)) -> rn.F3(FRn.get_three.b(a, d)):
  match d:
    case Wr.Got{+b, +s2}:
      rn.f3_c(a, b, fa, fb, Wr.get_nat(s2), rn.fn(s2))
    case Wr.Bad{}:
      Unit{}

def rn.f3_a(d: Wr.Dec<Nat>, fa: rn.FN(d)) -> rn.F3(FRn.get_three(d)):
  match d:
    case Wr.Got{+a, +s1}:
      rn.f3_b(a, fa, Wr.get_nat(s1), rn.fn(s1))
    case Wr.Bad{}:
      Unit{}

def rn.f3(+s: String) -> rn.F3(FRn.get_three(Wr.get_nat(s))):
  rn.f3_a(Wr.get_nat(s), rn.fn(s))

# ---- Cause ----

def rn.FCa(d: Wr.Dec<Rn.Cause>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {RetryNote.cause_fits(c) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rn.fca_rep_line(-p: Nat, fp: {LawsBase.wire_fits(p) == True{} : Bool}, d: Wr.Dec<String>, fl: rn.FS(d)) -> rn.FCa(FRn.get_repeated.line(p, d)):
  match d:
    case Wr.Got{+l, r}:
      rn.and2(LawsBase.wire_fits(p), LawsBase.wire_fits(String.length(l)), fp, fl)
    case Wr.Bad{}:
      Unit{}

def rn.fca_rep(d: Wr.Dec<Nat>, fp: rn.FN(d)) -> rn.FCa(FRn.get_repeated(d)):
  match d:
    case Wr.Got{+p, +s2}:
      rn.fca_rep_line(p, fp, Wr.get_str(s2), rn.fs(s2))
    case Wr.Bad{}:
      Unit{}

def rn.fca_len(d: Wr.Dec<FRn.Three>, f3: rn.F3(d)) -> rn.FCa(FRn.get_length(d)):
  match d:
    case Wr.Got{x, r}:
      match x:
        case FRn.Three{t, w, k}:
          f3
    case Wr.Bad{}:
      Unit{}

def rn.fca_lk_cap(-m: String, -why: String, -w: Nat, fs2: {Bool.and(LawsBase.wire_fits(String.length(m)), LawsBase.wire_fits(String.length(why))) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, d: Wr.Dec<Nat>, fk: rn.FN(d)) -> rn.FCa(FRn.get_leaked.cap(m, why, w, d)):
  match d:
    case Wr.Got{+k, r}:
      rn.and2(Bool.and(LawsBase.wire_fits(String.length(m)), LawsBase.wire_fits(String.length(why))), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(k)), fs2, rn.and2(LawsBase.wire_fits(w), LawsBase.wire_fits(k), fw, fk))
    case Wr.Bad{}:
      Unit{}

def rn.fca_lk_row(-m: String, -why: String, fs2: {Bool.and(LawsBase.wire_fits(String.length(m)), LawsBase.wire_fits(String.length(why))) == True{} : Bool}, d: Wr.Dec<Nat>, fw: rn.FN(d)) -> rn.FCa(FRn.get_leaked.row(m, why, d)):
  match d:
    case Wr.Got{+w, +s4}:
      rn.fca_lk_cap(m, why, w, fs2, fw, Wr.get_nat(s4), rn.fn(s4))
    case Wr.Bad{}:
      Unit{}

def rn.fca_lk_reason(-m: String, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, d: Wr.Dec<String>, fw: rn.FS(d)) -> rn.FCa(FRn.get_leaked.reason(m, d)):
  match d:
    case Wr.Got{+why, +s3}:
      rn.fca_lk_row(m, why, rn.and2(LawsBase.wire_fits(String.length(m)), LawsBase.wire_fits(String.length(why)), fm, fw), Wr.get_nat(s3), rn.fn(s3))
    case Wr.Bad{}:
      Unit{}

def rn.fca_lk(d: Wr.Dec<String>, fm: rn.FS(d)) -> rn.FCa(FRn.get_leaked(d)):
  match d:
    case Wr.Got{+m, +s2}:
      rn.fca_lk_reason(m, fm, Wr.get_str(s2), rn.fs(s2))
    case Wr.Bad{}:
      Unit{}

def rn.fca_rd_counts(-cs: List<&2, Rn.Call>, fl: {Bool.and(LawsBase.wire_fits(List.length(&2, Rn.Call, cs)), RetryNote.calls_fit(cs)) == True{} : Bool}, d: Wr.Dec<FRn.Three>, f3: rn.F3(d)) -> rn.FCa(FRn.get_redirect.counts(cs, d)):
  match d:
    case Wr.Got{x, r}:
      match x:
        case FRn.Three{+n, +w, +k}:
          rn.and2(Bool.and(LawsBase.wire_fits(List.length(&2, Rn.Call, cs)), RetryNote.calls_fit(cs)), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(k))), fl, f3)
    case Wr.Bad{}:
      Unit{}

def rn.fca_rd(d: Wr.Dec<List<&2, Rn.Call>>, fl: rn.FLS(d)) -> rn.FCa(FRn.get_redirect(d)):
  match d:
    case Wr.Got{+cs, +s2}:
      rn.fca_rd_counts(cs, fl, FRn.get_three(Wr.get_nat(s2)), rn.f3(s2))
    case Wr.Bad{}:
      Unit{}

def rn.fca_st(d: Wr.Dec<Nat>, fm: rn.FN(d)) -> rn.FCa(FRn.get_stalled(d)):
  match d:
    case Wr.Got{ms, r}:
      fm
    case Wr.Bad{}:
      Unit{}

def rn.fca_tag(d: Wr.Dec<Nat>) -> rn.FCa(FRn.get_cause(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          rn.fca_rep(Wr.get_nat(s1), rn.fn(s1))
        case 1n:
          {==}
        case 2n:
          rn.fca_len(FRn.get_three(Wr.get_nat(s1)), rn.f3(s1))
        case 3n:
          rn.fca_lk(Wr.get_str(s1), rn.fs(s1))
        case 4n:
          rn.fca_rd(Wr.get_list(~Rn.Call, ~FRn.get_call, s1), rn.fls(s1))
        case 5n:
          rn.fca_st(Wr.get_nat(s1), rn.fn(s1))
        case 6n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rn.fca(+s: String) -> rn.FCa(FRn.get_cause(Wr.get_nat(s))):
  rn.fca_tag(Wr.get_nat(s))

# ---- Req ----

def rn.FR(d: Wr.Dec<FRn.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {RetryNote.req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rn.fr_cause(-a: Nat, fa: {LawsBase.wire_fits(a) == True{} : Bool}, d: Wr.Dec<Rn.Cause>, fc: rn.FCa(d)) -> rn.FR(FRn.get_req.cause(a, d)):
  match d:
    case Wr.Got{+c, r}:
      rn.and2(LawsBase.wire_fits(a), RetryNote.cause_fits(c), fa, fc)
    case Wr.Bad{}:
      Unit{}

def rn.fr_top(d: Wr.Dec<Nat>, fa: rn.FN(d)) -> rn.FR(FRn.get_req(d)):
  match d:
    case Wr.Got{+a, +s1}:
      rn.fr_cause(a, fa, FRn.get_cause(Wr.get_nat(s1)), rn.fca(s1))
    case Wr.Bad{}:
      Unit{}

# every request the decoder reads fits the wire
def rn.fr(+s: String) -> rn.FR(FRn.get_req(Wr.get_nat(s))):
  rn.fr_top(Wr.get_nat(s), rn.fn(s))

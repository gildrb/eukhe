# eukhe: lemmas of area call_lift about the entry's wire: a spelled
# request that fits reads back whole (with the laws' reader), and the
# entry's encoders are the spec spellers (spec/harness/lift_wire.bend)

import Base
import ../../../bend/call_lift.bend as Cl
import ../../../bend/ffi_call_lift.bend as FCl
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/call_lift.bend as CallLift
import ../../../spec/harness/lift.bend as Sp
import ../../../spec/harness/lift_wire.bend as SpW
import ../../base/logic/bool.bend as LLogicBool
import ../../base/wire.bend as LWire
import ../../wire/wire_strs_spells.bend as PWireStrsSpells
import ../../wire/wire_strs_round_trip.bend as PWireStrsRoundTrip
import ../call_lift_refines_spec.bend as PCallLiftCallLiftRefinesSpec

# Requests
# --------

# a call that fits reads back, and the rest is untouched
def cle.call_rt(+c: Cl.Call, +rest: String, +h: {SpW.fit_call(c) == True{} : Bool}) -> {SpW.r_call(SpW.w_call(c, rest)) == Wr.Got{c, rest} : Wr.Dec<Cl.Call>}:
  match c:
    case Cl.Call{+f, +r, +ks}:
      +b = Wr.put_list(~String, ~Wr.put_str, ks, rest)
      +a = Wr.put_str(r, b)
      +hrk = LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(f)), Bool.and(LawsBase.wire_fits(String.length(r)), LawsBase.wire_strs_fit(ks)), h)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(f, a)), Wr.Got{f, a}, Wire.wire_str_round_trip(f, a, LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(f)), Bool.and(LawsBase.wire_fits(String.length(r)), LawsBase.wire_strs_fit(ks)), h))) : {SpW.r_call.fam(_) == Wr.Got{Cl.Call{f, r, ks}, rest} : Wr.Dec<Cl.Call>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(r, b)), Wr.Got{r, b}, Wire.wire_str_round_trip(r, b, LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(r)), LawsBase.wire_strs_fit(ks), hrk))) : {SpW.r_call.rev(f, _) == Wr.Got{Cl.Call{f, r, ks}, rest} : Wr.Dec<Cl.Call>}
      %Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, ks, rest), LawsBase.wire_spell_strs(ks, rest), Wire.wire_strs_spells(ks, rest)) : {SpW.r_call.keys(f, r, Wr.get_list(~String, ~Wr.get_str, _)) == Wr.Got{Cl.Call{f, r, ks}, rest} : Wr.Dec<Cl.Call>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, LawsBase.wire_spell_strs(ks, rest)), Wr.Got{ks, rest}, Wire.wire_strs_round_trip(ks, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(r)), LawsBase.wire_strs_fit(ks), hrk))) : {SpW.r_call.keys(f, r, _) == Wr.Got{Cl.Call{f, r, ks}, rest} : Wr.Dec<Cl.Call>}
      {==}

# the item loop reads back x then t
def cle.calls_rt(+t: List<&2, Cl.Call>, +x: Cl.Call, +rest: String, +hf: {SpW.fit_calls(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Cl.Call, ~SpW.r_call, List.length(&2, Cl.Call, t), SpW.r_call(SpW.w_call(x, SpW.w_calls(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cl.Call>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Cl.Call>, SpW.r_call(SpW.w_call(x, rest)), Wr.Got{x, rest}, cle.call_rt(x, rest, LLogicBool.wr_and_l(SpW.fit_call(x), True{}, hf))) : {Wr.get_list.go(~Cl.Call, ~SpW.r_call, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Cl.Call>>}
      {==}
    case Con{+y, +u}:
      +more = SpW.w_call(y, SpW.w_calls(u, rest))
      %Equal.sym(Wr.Dec<Cl.Call>, SpW.r_call(SpW.w_call(x, more)), Wr.Got{x, more}, cle.call_rt(x, more, LLogicBool.wr_and_l(SpW.fit_call(x), SpW.fit_calls(y <> u), hf))) : {Wr.get_list.go(~Cl.Call, ~SpW.r_call, 1n+List.length(&2, Cl.Call, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cl.Call>>}
      %Equal.sym(Wr.Dec<List<&2, Cl.Call>>, Wr.get_list.go(~Cl.Call, ~SpW.r_call, List.length(&2, Cl.Call, u), SpW.r_call(more)), Wr.Got{y <> u, rest}, cle.calls_rt(u, y, rest, LLogicBool.wr_and_r(SpW.fit_call(x), SpW.fit_calls(y <> u), hf))) : {Wr.get_list.cons(Cl.Call, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cl.Call>>}
      {==}

# a spelled request that fits reads back (with the laws' reader), and the
# rest is untouched
def cle.req_rt(+cs: List<&2, Cl.Call>, +rest: String, h: {SpW.fit_req(cs) == True{} : Bool}) -> {Wr.get_list(~Cl.Call, ~SpW.r_call, SpW.w_req(cs, rest)) == Wr.Got{cs, rest} : Wr.Dec<List<&2, Cl.Call>>}:
  match cs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Cl.Call, ~SpW.r_call, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Cl.Call>>}
      {==}
    case Con{+x, +t}:
      +hh = h
      +n = List.length(&2, Cl.Call, x <> t)
      +body = SpW.w_calls(x <> t, rest)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, body)), Wr.Got{n, body}, Wire.wire_nat_round_trip(n, body, LLogicBool.wr_and_l(LawsBase.wire_fits(n), SpW.fit_calls(x <> t), hh))) : {Wr.get_list.start(~Cl.Call, ~SpW.r_call, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cl.Call>>}
      cle.calls_rt(t, x, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(n), SpW.fit_calls(x <> t), hh))

# Replies
# -------

def cle.arg(a: Cl.Arg, -rest: String) -> {FCl.put_arg(a, rest) == SpW.w_arg(a, rest) : String}:
  match a:
    case Cl.Kept{i, k}:
      {==}
    case Cl.Added{k, j}:
      {==}

def cle.args_go(xs: List<&2, Cl.Arg>, -rest: String) -> {Wr.put_list.go(~Cl.Arg, ~FCl.put_arg, xs, rest) == (List.length(&2, Cl.Arg, xs), SpW.w_args.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Cl.Arg, ~FCl.put_arg, t, rest), (List.length(&2, Cl.Arg, t), SpW.w_args.items(t, rest)), cle.args_go(t, rest)) : {Wr.put_list.step(~Cl.Arg, ~FCl.put_arg, x, _) == (1n+List.length(&2, Cl.Arg, t), SpW.w_arg(x, SpW.w_args.items(t, rest))) : Nat & String}
      %cle.arg(x, SpW.w_args.items(t, rest)) : {(1n+List.length(&2, Cl.Arg, t), FCl.put_arg(x, SpW.w_args.items(t, rest))) == (1n+List.length(&2, Cl.Arg, t), _) : Nat & String}
      {==}

# the entry spells arguments as the spec does
def cle.args(+xs: List<&2, Cl.Arg>, -rest: String) -> {Wr.put_list(~Cl.Arg, ~FCl.put_arg, xs, rest) == SpW.w_args(xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Cl.Arg, ~FCl.put_arg, xs, rest), (List.length(&2, Cl.Arg, xs), SpW.w_args.items(xs, rest)), cle.args_go(xs, rest)) : {Wr.put_list.fin(_) == SpW.w_args(xs, rest) : String}
  {==}

def cle.receipt(x: Cl.Receipt, -rest: String) -> {FCl.put_receipt(x, rest) == SpW.w_receipt(x, rest) : String}:
  match x:
    case Cl.Renamed{a, b}:
      {==}
    case Cl.Clashed{a, b}:
      {==}
    case Cl.Filled{k}:
      {==}

def cle.receipts_go(xs: List<&2, Cl.Receipt>, -rest: String) -> {Wr.put_list.go(~Cl.Receipt, ~FCl.put_receipt, xs, rest) == (List.length(&2, Cl.Receipt, xs), SpW.w_receipts.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Cl.Receipt, ~FCl.put_receipt, t, rest), (List.length(&2, Cl.Receipt, t), SpW.w_receipts.items(t, rest)), cle.receipts_go(t, rest)) : {Wr.put_list.step(~Cl.Receipt, ~FCl.put_receipt, x, _) == (1n+List.length(&2, Cl.Receipt, t), SpW.w_receipt(x, SpW.w_receipts.items(t, rest))) : Nat & String}
      %cle.receipt(x, SpW.w_receipts.items(t, rest)) : {(1n+List.length(&2, Cl.Receipt, t), FCl.put_receipt(x, SpW.w_receipts.items(t, rest))) == (1n+List.length(&2, Cl.Receipt, t), _) : Nat & String}
      {==}

# the entry spells receipts as the spec does
def cle.receipts(+xs: List<&2, Cl.Receipt>, -rest: String) -> {Wr.put_list(~Cl.Receipt, ~FCl.put_receipt, xs, rest) == SpW.w_receipts(xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Cl.Receipt, ~FCl.put_receipt, xs, rest), (List.length(&2, Cl.Receipt, xs), SpW.w_receipts.items(xs, rest)), cle.receipts_go(xs, rest)) : {Wr.put_list.fin(_) == SpW.w_receipts(xs, rest) : String}
  {==}

# the entry spells a lift as the spec does
def cle.lift(l: Cl.Lift, +rest: String) -> {FCl.put_lift(l, rest) == SpW.w_lift(l, rest) : String}:
  match l:
    case Cl.Unknown{}:
      {==}
    case Cl.Current{}:
      {==}
    case Cl.Stranded{}:
      {==}
    case Cl.Lifted{+r, +a, +rs}:
      %cle.receipts(rs, rest) : {Wr.put_nat(3n, Wr.put_str(r, Wr.put_list(~Cl.Arg, ~FCl.put_arg, a, Wr.put_list(~Cl.Receipt, ~FCl.put_receipt, rs, rest)))) == Wr.put_nat(3n, Wr.put_str(r, SpW.w_args(a, _))) : String}
      %cle.args(a, Wr.put_list(~Cl.Receipt, ~FCl.put_receipt, rs, rest)) : {Wr.put_nat(3n, Wr.put_str(r, Wr.put_list(~Cl.Arg, ~FCl.put_arg, a, Wr.put_list(~Cl.Receipt, ~FCl.put_receipt, rs, rest)))) == Wr.put_nat(3n, Wr.put_str(r, _)) : String}
      {==}

# the entry spells the lifts by the shipped table as the spec's lifts
def cle.lifts(cs: List<&2, Cl.Call>, +rest: String) -> {FCl.put_lifts(Cl.table(), cs, rest) == SpW.w_lifts(cs, rest) : String}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +more}:
      %cle.lifts(more, rest) : {FCl.put_lift(Cl.lift(Cl.table(), c), FCl.put_lifts(Cl.table(), more, rest)) == SpW.w_lift(Sp.lift_spec(Cl.table(), c), _) : String}
      %CallLift.call_lift_refines_spec(Cl.table(), c) : {FCl.put_lift(Cl.lift(Cl.table(), c), FCl.put_lifts(Cl.table(), more, rest)) == SpW.w_lift(_, FCl.put_lifts(Cl.table(), more, rest)) : String}
      cle.lift(Cl.lift(Cl.table(), c), FCl.put_lifts(Cl.table(), more, rest))

# the entry's reply to cs is the spec's
def cle.answer(+cs: List<&2, Cl.Call>) -> {FCl.answer(cs) == SpW.w_reply(cs) : String}:
  %cle.lifts(cs, "") : {Wr.put_nat(List.length(&2, Cl.Call, cs), FCl.put_lifts(Cl.table(), cs, "")) == Wr.put_nat(List.length(&2, Cl.Call, cs), _) : String}
  {==}

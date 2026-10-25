# eukhe: lemmas of the proofs of area throttle

import Base
import ../../bend/throttle.bend as Th
import ../../bend/ffi_throttle.bend as FTh
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../base/wire.bend as LWire
import ../../laws/throttle.bend as Throttle

# ---- logic ----

def th.BD(b: Bool, T: Type, F: Type) -> Type:
  match b:
    case True{}:
      T
    case False{}:
      F

def th.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : th.BD(_, G, Unit)
  Unit{}

def th.absurd_t(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : th.BD(_, Unit, G)
  Unit{}

# ---- the reply ----

# one step of the entry's action encoder is the spec's speller
def th.put_step(x: Th.Act, -n: Nat, -r: String) -> {Wr.put_list.step(~Th.Act, ~FTh.put_act, x, (n, r)) == (1n+n, Throttle.spell_act(x, r)) : Nat & String}:
  match x:
    case Th.Keep{}:
      {==}
    case Th.Arm{}:
      {==}
    case Th.Commit{}:
      {==}
    case Th.Abort{}:
      {==}
    case Th.Await{}:
      {==}

# the entry's action encoder spells the count and the spec's items
def th.put_go(xs: List<&2, Th.Act>, -rest: String) -> {Wr.put_list.go(~Th.Act, ~FTh.put_act, xs, rest) == (List.length(&2, Th.Act, xs), Throttle.spell_acts.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Th.Act, ~FTh.put_act, t, rest), (List.length(&2, Th.Act, t), Throttle.spell_acts.items(t, rest)), th.put_go(t, rest)) : {Wr.put_list.step(~Th.Act, ~FTh.put_act, x, _) == (1n+List.length(&2, Th.Act, t), Throttle.spell_act(x, Throttle.spell_acts.items(t, rest))) : Nat & String}
      th.put_step(x, List.length(&2, Th.Act, t), Throttle.spell_acts.items(t, rest))

# the stepper's reply writer is the spec's speller
def th.of(m: Th.Moved) -> {FTh.step.of(m) == Throttle.spell_moved(m) : FTh.St & String}:
  match m:
    case Th.Moved{g, acts}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Th.Act, ~FTh.put_act, acts, ""), (List.length(&2, Th.Act, acts), Throttle.spell_acts.items(acts, "")), th.put_go(acts, "")) : {(FTh.Live{g}, Wr.put_list.fin(_)) == (FTh.Live{g}, Throttle.spell_acts(acts)) : FTh.St & String}
      {==}

# a step's answer is never the error form
def th.of_not_err(m: Th.Moved) -> {LawsBase.wire_opens_err(Throttle.reply(FTh.step.of(m))) == False{} : Bool}:
  match m:
    case Th.Moved{g, +acts}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Th.Act, ~FTh.put_act, acts, ""), (List.length(&2, Th.Act, acts), Throttle.spell_acts.items(acts, "")), th.put_go(acts, "")) : {LawsBase.wire_opens_err(Wr.put_list.fin(_)) == False{} : Bool}
      Wire.wire_nat_not_err(List.length(&2, Th.Act, acts), Throttle.spell_acts.items(acts, ""))

# ---- the event ----

def th.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

# a spelled event reads back
def th.ev_rt(+e: Th.Ev, +rest: String) -> {Wr.Got{e, rest} == FTh.get_ev(Wr.get_nat(Throttle.spell_ev(e, rest))) : Wr.Dec<Th.Ev>}:
  match e:
    case Th.Part{+b}:
      %th.nat(0n, Wr.put_bool(b, rest), {==}) : {Wr.Got{Th.Part{b}, rest} == FTh.get_ev(_) : Wr.Dec<Th.Ev>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest)) : {Wr.Got{Th.Part{b}, rest} == FTh.get_part(_) : Wr.Dec<Th.Ev>}
      {==}
    case Th.Fire{}:
      %th.nat(1n, rest, {==}) : {Wr.Got{Th.Fire{}, rest} == FTh.get_ev(_) : Wr.Dec<Th.Ev>}
      {==}
    case Th.Settle{}:
      %th.nat(2n, rest, {==}) : {Wr.Got{Th.Settle{}, rest} == FTh.get_ev(_) : Wr.Dec<Th.Ev>}
      {==}
    case Th.Finish{}:
      %th.nat(3n, rest, {==}) : {Wr.Got{Th.Finish{}, rest} == FTh.get_ev(_) : Wr.Dec<Th.Ev>}
      {==}
    case Th.Quit{}:
      %th.nat(4n, rest, {==}) : {Wr.Got{Th.Quit{}, rest} == FTh.get_ev(_) : Wr.Dec<Th.Ev>}
      {==}

# what the Nat decoder's answer says about its input s
def th.PNF(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String}
    case Wr.Bad{}:
      Unit

def th.pnf_go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> th.PNF(s, d):
  match d:
    case Wr.Got{+n, +r}:
      Wire.wire_nat_exact(s, n, r, ed)
    case Wr.Bad{}:
      Unit{}

def th.pnf(+s: String) -> th.PNF(s, Wr.get_nat(s)):
  th.pnf_go(s, Wr.get_nat(s), {==})

# what the event decoder's answer says about its input s
def th.PE(s: String, d: Wr.Dec<Th.Ev>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == Throttle.spell_ev(e, r) : String}
    case Wr.Bad{}:
      Unit

def th.pe_part(-s: String, +s1: String, e0: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> th.PE(s, FTh.get_part(d)):
  match d:
    case Wr.Got{+b, +r}:
      Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_bool(b, r)), e0, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_bool(b, r), Wire.wire_bool_exact(s1, b, r, ed)))
    case Wr.Bad{}:
      Unit{}

def th.pe_top(-s: String, d: Wr.Dec<Nat>, p: th.PNF(s, d)) -> th.PE(s, FTh.get_ev(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          th.pe_part(s, s1, p, Wr.get_bool(s1), {==})
        case 1n:
          p
        case 2n:
          p
        case 3n:
          p
        case 4n:
          p
        case 5n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every event the decoder reads is spelled
def th.pe(+s: String) -> th.PE(s, FTh.get_ev(Wr.get_nat(s))):
  th.pe_top(s, Wr.get_nat(s), th.pnf(s))

# eukhe: lemmas the reply reader proofs of area command share: what a
# reader accepts fits the wire (a list of strings, a list of Nats), and a
# spelling and a fit make the pair the exactness laws conclude.

import Base
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/command/entry.bend as Command
import ../../wire/base/spell.bend as LAWireSpell
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_strs_decoded_fit.bend as PWireStrsDecodedFit
import ../command_ffi_reads_only_requests.bend as PCommandFfiReadsOnlyRequests

# the claim of an exactness law: the input is the spelling, and it fits
def cr_pair(+s: String, +t: String, +b: Bool, c: {s == t : String} & {b == True{} : Bool}) -> {(s, b) == (t, True{}) : String & Bool}:
  (e1, e2) = c
  %Equal.sym(Bool, b, True{}, e2) : {(s, _) == (t, True{}) : String & Bool}
  %Equal.sym(String, s, t, e1) : {(_, True{}) == (t, True{}) : String & Bool}
  {==}

# a list of strings the reader accepts fits, as the entry's laws say it
def cr_strs_fit(+s: String, +p: List<&2, String>, +r: String, ed: {Wr.get_list(~String, ~Wr.get_str, s) == Wr.Got{p, r} : Wr.Dec<List<&2, String>>}) -> {Command.cmd_strs_fit(p) == True{} : Bool}:
  PCommandFfiReadsOnlyRequests.ci_strs_fit(p, Wire.wire_strs_decoded_fit(s, p, r, ed))

# ---- a list of Nats the reader accepts fits ----

# what the item loop's answer says (m + 1 items): every Nat fits
def cr_nl(m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {LawsBase.wire_nats_fit(xs) == True{} : Bool} & {List.length(&2, Nat, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def cr_nl_step(+x: Nat, -k: Nat, hx: {LawsBase.wire_fits(x) == True{} : Bool},
  d: Wr.Dec<List<&2, Nat>>, ih: cr_nl(k, d)) -> cr_nl(1n+k, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(ys), hx, e1),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Nat, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

def cr_nl_spec(m: Nat, cur: Wr.Dec<Nat>, +s: String, er: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) ->
  cr_nl(m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), True{}, Wire.wire_nat_decoded_fits(s, x, s3, er), {==}), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      cr_nl_step(x, k, Wire.wire_nat_decoded_fits(s, x, s3, er),
        Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(s3)), cr_nl_spec(k, Wr.get_nat(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder answer says: the count and every Nat fit
def cr_nf(d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cr_nf_conv(-m: Nat, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, nl: cr_nl(m, d)) -> cr_nf(d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = nl
      %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
      LAWireSpell.ws_and_tt(LawsBase.wire_fits(1n+m), LawsBase.wire_nats_fit(xs), hn, e1)
    case Wr.Bad{}:
      Unit{}

def cr_nf_nat(n: Nat, +s2: String, hn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  cr_nf(Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s2})):
  match n:
    case 0n:
      {==}
    case 1n++m:
      cr_nf_conv(m, hn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s2)), cr_nl_spec(m, Wr.get_nat(s2), s2, {==}))

def cr_nf_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) ->
  cr_nf(Wr.get_list.start(~Nat, ~Wr.get_nat, r)):
  match r:
    case Wr.Got{+n, +s2}:
      cr_nf_nat(n, s2, Wire.wire_nat_decoded_fits(s, n, s2, er))
    case Wr.Bad{}:
      Unit{}

def cr_nf_at(+s: String, -d: Wr.Dec<List<&2, Nat>>, er: {Wr.get_list(~Nat, ~Wr.get_nat, s) == d : Wr.Dec<List<&2, Nat>>}) -> cr_nf(d):
  %er : cr_nf(_)
  cr_nf_top(s, Wr.get_nat(s), {==})

# a list of Nats the reader accepts fits: its count and every Nat
def cr_nats_fit(+s: String, +xs: List<&2, Nat>, -r: String, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == Wr.Got{xs, r} : Wr.Dec<List<&2, Nat>>}) ->
  {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}:
  cr_nf_at(s, Wr.Got{xs, r}, ed)

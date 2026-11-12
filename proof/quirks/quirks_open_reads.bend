# eukhe: the proof of LAW quirks_open_reads
#
# PROOF: each list the open's decoder reads is the spelling of that list,
# within the wire (Wire.wire_list_exact, WireFfi.wrb.nats_fit); the flat
# list a rulebook is read from is the spelling of that rulebook (qor.rules:
# four Nats per rule, a layer tag below 3); a reply other than the error
# form comes only from a rulebook read whole, nothing left.

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/quirks.bend as Quirks
import ../wire/base/spell.bend as LAWireSpell
import ../wire_ffi/base.bend as WRB
import ./base/verdicts.bend as QV

# The rules, read back
# --------------------

# the layer a tag reads as is spelled by that tag
def qor.lay(l: Nat, -L: If.Lay, e: {FQ.lay(l) == Some{L} : Maybe<&2, If.Lay>}) -> {l == Quirks.qs_lay(L) : Nat}:
  match l:
    case 0n:
      %QV.qv.some_inj(If.Lay, If.Fam{}, L, e) : {0n == Quirks.qs_lay(_) : Nat}
      {==}
    case 1n:
      %QV.qv.some_inj(If.Lay, If.Mod{}, L, e) : {1n == Quirks.qs_lay(_) : Nat}
      {==}
    case 2n:
      %QV.qv.some_inj(If.Lay, If.Host{}, L, e) : {2n == Quirks.qs_lay(_) : Nat}
      {==}
    case 3n+p:
      QV.qv.none_some(If.Lay, {3n+p == Quirks.qs_lay(L) : Nat}, L, e)

# the rules m read from xs are spelled by xs
def qor.RL(xs: List<&2, Nat>, m: Maybe<&2, List<&2, If.Rule>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{rs}:
      {xs == Quirks.qs_flat(rs) : List<&2, Nat>}

# a rule's four Nats, then the rest, spell that rule, then the rest's rules
def qor.step(+l: Nat, +t: Nat, +d: Nat, +v: Nat, +rest: List<&2, Nat>, -L: If.Lay, -rs: List<&2, If.Rule>, el: {l == Quirks.qs_lay(L) : Nat}, ih: {rest == Quirks.qs_flat(rs) : List<&2, Nat>}) -> {l <> t <> d <> v <> rest == Quirks.qs_lay(L) <> t <> d <> v <> Quirks.qs_flat(rs) : List<&2, Nat>}:
  %ih : {l <> t <> d <> v <> rest == Quirks.qs_lay(L) <> t <> d <> v <> _ : List<&2, Nat>}
  %el : {l <> t <> d <> v <> rest == _ <> t <> d <> v <> rest : List<&2, Nat>}
  {==}

def qor.cons(+l: Nat, +t: Nat, +d: Nat, +v: Nat, +rest: List<&2, Nat>, ml: Maybe<&2, If.Lay>, el: {FQ.lay(l) == ml : Maybe<&2, If.Lay>}, mr: Maybe<&2, List<&2, If.Rule>>, ih: qor.RL(rest, mr)) -> qor.RL(l <> t <> d <> v <> rest, FQ.rules.cons(ml, t, d, v, mr)):
  match ml:
    case None{}:
      Unit{}
    case Some{ly}:
      match mr:
        case None{}:
          Unit{}
        case Some{rs}:
          qor.step(l, t, d, v, rest, ly, rs, qor.lay(l, ly, el), ih)

def qor.rules(xs: List<&2, Nat>) -> qor.RL(xs, FQ.rules(xs)):
  match xs:
    case Nil{}:
      {==}
    case +l <> a:
      match a:
        case Nil{}:
          Unit{}
        case t <> b:
          match b:
            case Nil{}:
              Unit{}
            case d <> c:
              match c:
                case Nil{}:
                  Unit{}
                case v <> +rest:
                  qor.cons(l, t, d, v, rest, FQ.lay(l), {==}, FQ.rules(rest), qor.rules(rest))

# The open, read back
# -------------------

def qor.G(s: String) -> Type:
  &known: List<&2, Nat> -> &rs: List<&2, If.Rule> -> {s == Quirks.spell_open(known, rs) : String} & {Quirks.open_fits(known, rs) == True{} : Bool}

# the rulebook rs read from xs, spelled
def qor.fin(-s: String, +known: List<&2, Nat>, -s1: String, +xs: List<&2, Nat>, +rs: List<&2, If.Rule>,
  ek: {s == Wr.put_list(~Nat, ~Wr.put_nat, known, s1) : String},
  fk: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, known)), LawsBase.wire_nats_fit(known)) == True{} : Bool},
  ex: {s1 == Wr.put_list(~Nat, ~Wr.put_nat, xs, "") : String},
  fx: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool},
  +rl: {xs == Quirks.qs_flat(rs) : List<&2, Nat>}) -> qor.G(s):
  +e1 = Equal.trans(String, s, Wr.put_list(~Nat, ~Wr.put_nat, known, s1), Wr.put_list(~Nat, ~Wr.put_nat, known, Wr.put_list(~Nat, ~Wr.put_nat, xs, "")), ek, Equal.cong(String, String, z => Wr.put_list(~Nat, ~Wr.put_nat, known, z), s1, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""), ex))
  +e2 = Equal.trans(String, s, Wr.put_list(~Nat, ~Wr.put_nat, known, Wr.put_list(~Nat, ~Wr.put_nat, xs, "")), Quirks.spell_open(known, rs), e1, Equal.cong(List<&2, Nat>, String, z => Wr.put_list(~Nat, ~Wr.put_nat, known, Wr.put_list(~Nat, ~Wr.put_nat, z, "")), xs, Quirks.qs_flat(rs), rl))
  +fr = Equal.trans(Bool, Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Quirks.qs_flat(rs))), LawsBase.wire_nats_fit(Quirks.qs_flat(rs))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), True{}, Equal.cong(List<&2, Nat>, Bool, z => Bool.and(LawsBase.wire_fits(List.length(&2, Nat, z)), LawsBase.wire_nats_fit(z)), Quirks.qs_flat(rs), xs, Equal.sym(List<&2, Nat>, xs, Quirks.qs_flat(rs), rl)), fx)
  (known, (rs, (e2, LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, known)), LawsBase.wire_nats_fit(known)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Quirks.qs_flat(rs))), LawsBase.wire_nats_fit(Quirks.qs_flat(rs))), fk, fr))))

def qor.book(-s: String, +known: List<&2, Nat>, -s1: String, +xs: List<&2, Nat>,
  ek: {s == Wr.put_list(~Nat, ~Wr.put_nat, known, s1) : String},
  fk: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, known)), LawsBase.wire_nats_fit(known)) == True{} : Bool},
  ex: {s1 == Wr.put_list(~Nat, ~Wr.put_nat, xs, "") : String},
  fx: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool},
  m: Maybe<&2, List<&2, If.Rule>>, rl: qor.RL(xs, m),
  ok: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.open.book(known, m))) == False{} : Bool}) -> qor.G(s):
  match m:
    case None{}:
      LAWireSpell.ws_absurd(qor.G(s), ok)
    case Some{+rs}:
      qor.fin(s, known, s1, xs, rs, ek, fk, ex, fx, rl)

def qor.end(-s: String, +known: List<&2, Nat>, -s1: String, +xs: List<&2, Nat>, s2: String,
  ek: {s == Wr.put_list(~Nat, ~Wr.put_nat, known, s1) : String},
  fk: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, known)), LawsBase.wire_nats_fit(known)) == True{} : Bool},
  ex: {s1 == Wr.put_list(~Nat, ~Wr.put_nat, xs, s2) : String},
  fx: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool},
  ok: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.open.end(Wr.end(s2), known, xs))) == False{} : Bool}) -> qor.G(s):
  match s2:
    case SNil{}:
      qor.book(s, known, s1, xs, ek, fk, ex, fx, FQ.rules(xs), qor.rules(xs), ok)
    case SCon{c, t}:
      LAWireSpell.ws_absurd(qor.G(s), ok)

def qor.rules_d(-s: String, +known: List<&2, Nat>, +s1: String,
  ek: {s == Wr.put_list(~Nat, ~Wr.put_nat, known, s1) : String},
  fk: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, known)), LawsBase.wire_nats_fit(known)) == True{} : Bool},
  d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>},
  ok: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.open.rules(known, d))) == False{} : Bool}) -> qor.G(s):
  match d:
    case Wr.Got{+xs, +s2}:
      +e = ed
      qor.end(s, known, s1, xs, s2, ek, fk, Wire.wire_list_exact(s1, xs, s2, e), WRB.wrb.nats_fit(s1, xs, s2, e), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(qor.G(s), ok)

def qor.known(+s: String, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == d : Wr.Dec<List<&2, Nat>>},
  ok: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.open.known(d))) == False{} : Bool}) -> qor.G(s):
  match d:
    case Wr.Got{+known, +s1}:
      +e = ed
      qor.rules_d(s, known, s1, Wire.wire_list_exact(s, known, s1, e), WRB.wrb.nats_fit(s, known, s1, e), Wr.get_list(~Nat, ~Wr.get_nat, s1), {==}, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(qor.G(s), ok)

def Quirks.quirks_open_reads(s, ok):
  qor.known(s, Wr.get_list(~Nat, ~Wr.get_nat, s), {==}, ok)

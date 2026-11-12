# eukhe: the proof of LAW approvals_desk_entry_only_events
#
# PROOF: whatever the decoder (FAm.get_ev) reads is the input spelled as
# Rust spells it, then what follows, and fits the wire: each decoder stage,
# given what its wire reader read, turns the input into the spelling of
# that part (the wire's exactness laws: wire_nat_exact, wire_str_exact,
# wire_list_exact, wire_bool_exact), and the Nats, ids and effects it read
# fit (wire_nat_decoded_fits, wire_str_decoded_fits, and a decoded list of
# Nats fits: LWb.wrb.nats_fit). A Here or Fate code past the known ones,
# or a tag past 4, is refused by the decoder. So an input read whole is
# one spelled event; any other input (refused by the decoder, or with
# input left after the event) keeps the desk and answers the error form.

import Base
import ../../bend/approvals.bend as Am
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/approvals/entry.bend as ApprovalsEntry
import ../wire/wire_nat_exact.bend as PWNatExact
import ../wire/wire_str_exact.bend as PWStrExact
import ../wire/wire_list_exact.bend as PWListExact
import ../wire/wire_bool_exact.bend as PWBoolExact
import ../wire/wire_nat_decoded_fits.bend as PWNatFits
import ../wire/wire_str_decoded_fits.bend as PWStrFits
import ../wire_ffi/base.bend as LWb

# what the decoder read is the input spelled, and fits
def oe.C(d: Wr.Dec<Am.Ev>, s: String) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == ApprovalsEntry.spell_ev(e, r) : String} & {ApprovalsEntry.ev_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# s spelled up to a field a is s spelled up to its spelling b
def oe.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

def oe.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      ea

# An ask: id, effects, here, parent
# ---------------------------------

def oe.parent(+s: String, +id: String, +es: List<&2, Nat>, +h: Am.Here, +s4: String, pre: {s == Wr.put_nat(0n, Wr.put_str(id, Wr.put_list(~Nat, ~Wr.put_nat, es, Wr.put_nat(ApprovalsEntry.spell_here(h), s4)))) : String}, f1: {LawsBase.wire_fits(String.length(id)) == True{} : Bool}, f2: {ApprovalsEntry.ns_fit(es) == True{} : Bool}, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(s4) == d : Wr.Dec<Bool>}) -> oe.C(FAm.ask.parent(id, es, h, d), s):
  match d:
    case Wr.Got{+p, +s5}:
      (oe.step(z => Wr.put_nat(0n, Wr.put_str(id, Wr.put_list(~Nat, ~Wr.put_nat, es, Wr.put_nat(ApprovalsEntry.spell_here(h), z)))), s, s4, Wr.put_bool(p, s5), pre, Wire.wire_bool_exact(s4, p, s5, ed)), oe.and_t(LawsBase.wire_fits(String.length(id)), ApprovalsEntry.ns_fit(es), f1, f2))
    case Wr.Bad{}:
      Unit{}

def oe.here(+s: String, +id: String, +es: List<&2, Nat>, +s3: String, pre: {s == Wr.put_nat(0n, Wr.put_str(id, Wr.put_list(~Nat, ~Wr.put_nat, es, s3))) : String}, f1: {LawsBase.wire_fits(String.length(id)) == True{} : Bool}, f2: {ApprovalsEntry.ns_fit(es) == True{} : Bool}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> oe.C(FAm.ask.here(id, es, FAm.get_here(d)), s):
  match d:
    case Wr.Got{+c, +s4}:
      match c:
        case 0n:
          oe.parent(s, id, es, Am.Nobody{}, s4, oe.step(z => Wr.put_nat(0n, Wr.put_str(id, Wr.put_list(~Nat, ~Wr.put_nat, es, z))), s, s3, Wr.put_nat(0n, s4), pre, Wire.wire_nat_exact(s3, 0n, s4, ed)), f1, f2, Wr.get_bool(s4), {==})
        case 1n:
          oe.parent(s, id, es, Am.GatewayOnly{}, s4, oe.step(z => Wr.put_nat(0n, Wr.put_str(id, Wr.put_list(~Nat, ~Wr.put_nat, es, z))), s, s3, Wr.put_nat(1n, s4), pre, Wire.wire_nat_exact(s3, 1n, s4, ed)), f1, f2, Wr.get_bool(s4), {==})
        case 2n:
          oe.parent(s, id, es, Am.Clients{}, s4, oe.step(z => Wr.put_nat(0n, Wr.put_str(id, Wr.put_list(~Nat, ~Wr.put_nat, es, z))), s, s3, Wr.put_nat(2n, s4), pre, Wire.wire_nat_exact(s3, 2n, s4, ed)), f1, f2, Wr.get_bool(s4), {==})
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def oe.effs(+s: String, +id: String, +s2: String, pre: {s == Wr.put_nat(0n, Wr.put_str(id, s2)) : String}, f1: {LawsBase.wire_fits(String.length(id)) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, +ed: {Wr.get_list(~Nat, ~Wr.get_nat, s2) == d : Wr.Dec<List<&2, Nat>>}) -> oe.C(FAm.ask.effs(id, d), s):
  match d:
    case Wr.Got{+es, +s3}:
      oe.here(s, id, es, s3, oe.step(z => Wr.put_nat(0n, Wr.put_str(id, z)), s, s2, Wr.put_list(~Nat, ~Wr.put_nat, es, s3), pre, Wire.wire_list_exact(s2, es, s3, ed)), f1, LWb.wrb.nats_fit(s2, es, s3, ed), Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def oe.ask(+s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, +ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> oe.C(FAm.ask.id(d), s):
  match d:
    case Wr.Got{+id, +s2}:
      oe.effs(s, id, s2, oe.step(z => Wr.put_nat(0n, z), s, s1, Wr.put_str(id, s2), pre, Wire.wire_str_exact(s1, id, s2, ed)), Wire.wire_str_decoded_fits(s1, id, s2, ed), Wr.get_list(~Nat, ~Wr.get_nat, s2), {==})
    case Wr.Bad{}:
      Unit{}

# An answer: id, yes
# ------------------

def oe.answer.yes(+s: String, +id: String, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_str(id, s2)) : String}, f1: {LawsBase.wire_fits(String.length(id)) == True{} : Bool}, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> oe.C(FAm.answer.yes(id, d), s):
  match d:
    case Wr.Got{+y, +s3}:
      (oe.step(z => Wr.put_nat(1n, Wr.put_str(id, z)), s, s2, Wr.put_bool(y, s3), pre, Wire.wire_bool_exact(s2, y, s3, ed)), f1)
    case Wr.Bad{}:
      Unit{}

def oe.answer(+s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, +ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> oe.C(FAm.answer.id(d), s):
  match d:
    case Wr.Got{+id, +s2}:
      oe.answer.yes(s, id, s2, oe.step(z => Wr.put_nat(1n, z), s, s1, Wr.put_str(id, s2), pre, Wire.wire_str_exact(s1, id, s2, ed)), Wire.wire_str_decoded_fits(s1, id, s2, ed), Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

# A detach: here, parent
# ----------------------

def oe.detach.p(+s: String, +h: Am.Here, +s2: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(ApprovalsEntry.spell_here(h), s2)) : String}, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> oe.C(FAm.detach.parent(h, d), s):
  match d:
    case Wr.Got{+p, +s3}:
      (oe.step(z => Wr.put_nat(2n, Wr.put_nat(ApprovalsEntry.spell_here(h), z)), s, s2, Wr.put_bool(p, s3), pre, Wire.wire_bool_exact(s2, p, s3, ed)), {==})
    case Wr.Bad{}:
      Unit{}

def oe.detach(+s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> oe.C(FAm.detach.here(FAm.get_here(d)), s):
  match d:
    case Wr.Got{+c, +s2}:
      match c:
        case 0n:
          oe.detach.p(s, Am.Nobody{}, s2, oe.step(z => Wr.put_nat(2n, z), s, s1, Wr.put_nat(0n, s2), pre, Wire.wire_nat_exact(s1, 0n, s2, ed)), Wr.get_bool(s2), {==})
        case 1n:
          oe.detach.p(s, Am.GatewayOnly{}, s2, oe.step(z => Wr.put_nat(2n, z), s, s1, Wr.put_nat(1n, s2), pre, Wire.wire_nat_exact(s1, 1n, s2, ed)), Wr.get_bool(s2), {==})
        case 2n:
          oe.detach.p(s, Am.Clients{}, s2, oe.step(z => Wr.put_nat(2n, z), s, s1, Wr.put_nat(2n, s2), pre, Wire.wire_nat_exact(s1, 2n, s2, ed)), Wr.get_bool(s2), {==})
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# A cancel: key
# -------------

def oe.cancel(+s: String, +s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> oe.C(FAm.cancel.key(d), s):
  match d:
    case Wr.Got{+k, +s2}:
      (oe.step(z => Wr.put_nat(3n, z), s, s1, Wr.put_nat(k, s2), pre, Wire.wire_nat_exact(s1, k, s2, ed)), Wire.wire_nat_decoded_fits(s1, k, s2, ed))
    case Wr.Bad{}:
      Unit{}

# The parent's answer: key, fate
# ------------------------------

def oe.back.f(+s: String, +k: Nat, +s2: String, pre: {s == Wr.put_nat(4n, Wr.put_nat(k, s2)) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> oe.C(FAm.back.fate(k, FAm.get_fate(d)), s):
  match d:
    case Wr.Got{+c, +s3}:
      match c:
        case 0n:
          (oe.step(z => Wr.put_nat(4n, Wr.put_nat(k, z)), s, s2, Wr.put_nat(0n, s3), pre, Wire.wire_nat_exact(s2, 0n, s3, ed)), fk)
        case 1n:
          (oe.step(z => Wr.put_nat(4n, Wr.put_nat(k, z)), s, s2, Wr.put_nat(1n, s3), pre, Wire.wire_nat_exact(s2, 1n, s3, ed)), fk)
        case 2n:
          (oe.step(z => Wr.put_nat(4n, Wr.put_nat(k, z)), s, s2, Wr.put_nat(2n, s3), pre, Wire.wire_nat_exact(s2, 2n, s3, ed)), fk)
        case 3n:
          (oe.step(z => Wr.put_nat(4n, Wr.put_nat(k, z)), s, s2, Wr.put_nat(3n, s3), pre, Wire.wire_nat_exact(s2, 3n, s3, ed)), fk)
        case 4n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def oe.back(+s: String, +s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> oe.C(FAm.back.key(d), s):
  match d:
    case Wr.Got{+k, +s2}:
      oe.back.f(s, k, s2, oe.step(z => Wr.put_nat(4n, z), s, s1, Wr.put_nat(k, s2), pre, Wire.wire_nat_exact(s1, k, s2, ed)), Wire.wire_nat_decoded_fits(s1, k, s2, ed), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

# The tag
# -------

def oe.tag(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> oe.C(FAm.get_ev.go(d), s):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          oe.ask(s, s1, Wire.wire_nat_exact(s, 0n, s1, ed), Wr.get_str(s1), {==})
        case 1n:
          oe.answer(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_str(s1), {==})
        case 2n:
          oe.detach(s, s1, Wire.wire_nat_exact(s, 2n, s1, ed), Wr.get_nat(s1), {==})
        case 3n:
          oe.cancel(s, s1, Wire.wire_nat_exact(s, 3n, s1, ed), Wr.get_nat(s1), {==})
        case 4n:
          oe.back(s, s1, Wire.wire_nat_exact(s, 4n, s1, ed), Wr.get_nat(s1), {==})
        case 5n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the decoder reads is s spelled, and fits
def oe.read(+s: String) -> oe.C(FAm.get_ev(s), s):
  oe.tag(s, Wr.get_nat(s), {==})

# The law
# -------

# an input the decoder does not read whole keeps the desk
def oe.keep(+d: Am.D, +s: String, -r: Wr.Dec<Am.Ev>, hr: {FAm.get_ev(s) == r : Wr.Dec<Am.Ev>}, k: {FAm.step.ev(d, r) == (FAm.Live{d}, ApprovalsEntry.malformed_event()) : FAm.St & String}) -> {FAm.step(FAm.Live{d}, s) == (FAm.Live{d}, ApprovalsEntry.malformed_event()) : FAm.St & String}:
  %Equal.sym(Wr.Dec<Am.Ev>, FAm.get_ev(s), r, hr) : {FAm.step.ev(d, _) == (FAm.Live{d}, ApprovalsEntry.malformed_event()) : FAm.St & String}
  k

# an input the decoder reads whole is the spelling of the event it read
def oe.at(+s: String, +e: Am.Ev, hr: {FAm.get_ev(s) == Wr.Got{e, ""} : Wr.Dec<Am.Ev>}) -> oe.C(Wr.Got{e, ""}, s):
  %hr : oe.C(_, s)
  oe.read(s)

def oe.flip(-s: String, -e: Am.Ev, c: {s == ApprovalsEntry.spell_ev(e, "") : String} & {ApprovalsEntry.ev_fits(e) == True{} : Bool}) -> {ApprovalsEntry.spell_ev(e, "") == s : String} & {ApprovalsEntry.ev_fits(e) == True{} : Bool}:
  (a, b) = c
  (Equal.sym(String, s, ApprovalsEntry.spell_ev(e, ""), a), b)

def oe.ans(+d: Am.D, +s: String, r: Wr.Dec<Am.Ev>, hr: {FAm.get_ev(s) == r : Wr.Dec<Am.Ev>}) -> ApprovalsEntry.dk_refused_or_event(d, s):
  match r:
    case Wr.Got{+e, rest}:
      match rest:
        case SNil{}:
          Inr{(e, oe.flip(s, e, oe.at(s, e, hr)))}
        case SCon{c, t}:
          Inl{oe.keep(d, s, Wr.Got{e, SCon{c, t}}, hr, {==})}
    case Wr.Bad{}:
      Inl{oe.keep(d, s, Wr.Bad{}, hr, {==})}

def ApprovalsEntry.approvals_desk_entry_only_events(d, s):
  oe.ans(d, s, FAm.get_ev(s), {==})

# eukhe: lemmas the proofs of the approvals entry share
# (laws/approvals/entry.bend)
#
# The entry's decoder is the laws' reader, stage by stage (ae.read_*);
# its encoders are the laws' spellers (ae.put_*); so a live desk's step is
# the spec's on every input (ae.exact). The reader reads back every event
# Rust spells (ae.rt: tags and booleans compute, a request id reads back
# by wire_str_round_trip, the effects by wire_list_round_trip, a key by
# wire_nat_round_trip).

import Base
import ../../../bend/approvals.bend as Am
import ../../../bend/ffi_approvals.bend as FAm
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/approvals/entry.bend as ApprovalsEntry
import ../../../laws/wire.bend as Wire
import ../../base/wire.bend as LWire

# The decoder is the reader
# -------------------------

def ae.here(r: Wr.Dec<Nat>) -> {FAm.get_here(r) == ApprovalsEntry.read_here(r) : Wr.Dec<Am.Here>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def ae.fate(r: Wr.Dec<Nat>) -> {FAm.get_fate(r) == ApprovalsEntry.read_fate(r) : Wr.Dec<Am.Fate>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n+u:
          {==}
    case Wr.Bad{}:
      {==}

def ae.ask_parent(id: String, es: List<&2, Nat>, h: Am.Here, r: Wr.Dec<Bool>) -> {FAm.ask.parent(id, es, h, r) == ApprovalsEntry.read_ask.parent(id, es, h, r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.ask_here(id: String, es: List<&2, Nat>, r: Wr.Dec<Am.Here>) -> {FAm.ask.here(id, es, r) == ApprovalsEntry.read_ask.here(id, es, r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{h, s}:
      ae.ask_parent(id, es, h, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ae.ask_effs(+id: String, r: Wr.Dec<List<&2, Nat>>) -> {FAm.ask.effs(id, r) == ApprovalsEntry.read_ask.effs(id, r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{+es, +s}:
      %ae.here(Wr.get_nat(s)) : {FAm.ask.here(id, es, FAm.get_here(Wr.get_nat(s))) == ApprovalsEntry.read_ask.here(id, es, _) : Wr.Dec<Am.Ev>}
      ae.ask_here(id, es, FAm.get_here(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def ae.ask_id(r: Wr.Dec<String>) -> {FAm.ask.id(r) == ApprovalsEntry.read_ask.id(r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{id, s}:
      ae.ask_effs(id, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def ae.answer_yes(id: String, r: Wr.Dec<Bool>) -> {FAm.answer.yes(id, r) == ApprovalsEntry.read_answer.yes(id, r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{y, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.answer_id(r: Wr.Dec<String>) -> {FAm.answer.id(r) == ApprovalsEntry.read_answer.id(r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{id, s}:
      ae.answer_yes(id, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ae.detach_parent(h: Am.Here, r: Wr.Dec<Bool>) -> {FAm.detach.parent(h, r) == ApprovalsEntry.read_detach.parent(h, r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.detach_here(r: Wr.Dec<Am.Here>) -> {FAm.detach.here(r) == ApprovalsEntry.read_detach.here(r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{h, s}:
      ae.detach_parent(h, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ae.cancel_key(r: Wr.Dec<Nat>) -> {FAm.cancel.key(r) == ApprovalsEntry.read_cancel.key(r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.back_fate(k: Nat, r: Wr.Dec<Am.Fate>) -> {FAm.back.fate(k, r) == ApprovalsEntry.read_back.fate(k, r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ae.back_key(r: Wr.Dec<Nat>) -> {FAm.back.key(r) == ApprovalsEntry.read_back.key(r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{+k, +s}:
      %ae.fate(Wr.get_nat(s)) : {FAm.back.fate(k, FAm.get_fate(Wr.get_nat(s))) == ApprovalsEntry.read_back.fate(k, _) : Wr.Dec<Am.Ev>}
      ae.back_fate(k, FAm.get_fate(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def ae.tag(t: Nat, +s: String) -> {FAm.get_ev.tag(t, s) == ApprovalsEntry.read_ev.tag(t, s) : Wr.Dec<Am.Ev>}:
  match t:
    case 0n:
      ae.ask_id(Wr.get_str(s))
    case 1n:
      ae.answer_id(Wr.get_str(s))
    case 2n:
      %ae.here(Wr.get_nat(s)) : {FAm.detach.here(FAm.get_here(Wr.get_nat(s))) == ApprovalsEntry.read_detach.here(_) : Wr.Dec<Am.Ev>}
      ae.detach_here(FAm.get_here(Wr.get_nat(s)))
    case 3n:
      ae.cancel_key(Wr.get_nat(s))
    case 4n:
      ae.back_key(Wr.get_nat(s))
    case 5n+u:
      {==}

def ae.go(r: Wr.Dec<Nat>) -> {FAm.get_ev.go(r) == ApprovalsEntry.read_ev.go(r) : Wr.Dec<Am.Ev>}:
  match r:
    case Wr.Got{t, s}:
      ae.tag(t, s)
    case Wr.Bad{}:
      {==}

# the entry reads every input as the laws' reader does
def ae.read(+s: String) -> {FAm.get_ev(s) == ApprovalsEntry.read_ev(s) : Wr.Dec<Am.Ev>}:
  ae.go(Wr.get_nat(s))

# The encoders are the spellers
# -----------------------------

def ae.put_fate(f: Am.Fate, rest: String) -> {FAm.put_fate(f, rest) == ApprovalsEntry.spell_fate(f, rest) : String}:
  match f:
    case Am.Runs{}:
      {==}
    case Am.Denied{}:
      {==}
    case Am.Unheard{}:
      {==}
    case Am.GatewayRefused{}:
      {==}

def ae.put_act(a: Am.Act, +rest: String) -> {FAm.put_act(a, rest) == ApprovalsEntry.spell_act(a, rest) : String}:
  match a:
    case Am.AShow{k}:
      {==}
    case Am.ASettle{k}:
      {==}
    case Am.ARelay{k}:
      {==}
    case Am.AWake{+k, +f}:
      %ae.put_fate(f, rest) : {Wr.put_nat(3n, Wr.put_nat(k, FAm.put_fate(f, rest))) == Wr.put_nat(3n, Wr.put_nat(k, _)) : String}
      {==}
    case Am.ATook{}:
      {==}
    case Am.AGone{}:
      {==}

def ae.items(as: List<&2, Am.Act>) -> {FAm.put_acts.go(as, "") == ApprovalsEntry.spell_acts.items(as) : String}:
  match as:
    case Nil{}:
      {==}
    case +a <> +t:
      %ae.items(t) : {FAm.put_act(a, FAm.put_acts.go(t, "")) == ApprovalsEntry.spell_act(a, _) : String}
      ae.put_act(a, FAm.put_acts.go(t, ""))

def ae.acts(+as: List<&2, Am.Act>) -> {FAm.put_acts(as) == ApprovalsEntry.spell_acts(as) : String}:
  %ae.items(as) : {Wr.put_nat(List.length(&2, Am.Act, as), FAm.put_acts.go(as, "")) == Wr.put_nat(List.length(&2, Am.Act, as), _) : String}
  {==}

def ae.reply(e: Am.Ev, +n: Nat, +as: List<&2, Am.Act>) -> {FAm.put_reply(e, n, as) == ApprovalsEntry.spell_reply(e, n, as) : String}:
  match e:
    case Am.EAsk{id, es, h, p}:
      %ae.acts(as) : {Wr.put_nat(n, FAm.put_acts(as)) == Wr.put_nat(n, _) : String}
      {==}
    case Am.EAnswer{id, y}:
      ae.acts(as)
    case Am.EDetach{h, p}:
      ae.acts(as)
    case Am.ECancel{k}:
      ae.acts(as)
    case Am.EBack{k, f}:
      ae.acts(as)

# The step is the spec's
# ----------------------

def ae.step_reply(+e: Am.Ev, +n: Nat, r: Am.D & List<&2, Am.Act>) -> {FAm.step.reply(e, n, r) == ApprovalsEntry.dk_reply(e, n, r) : FAm.St & String}:
  (d2, +as) = r
  %ae.reply(e, n, as) : {(FAm.Live{d2}, FAm.put_reply(e, n, as)) == (FAm.Live{d2}, _) : FAm.St & String}
  {==}

def ae.next(d: Am.D) -> {FAm.D.next(d) == ApprovalsEntry.dk_next(d) : Nat}:
  match d:
    case Am.D{n, qs}:
      {==}

def ae.end(b: Bool, +d: Am.D, +e: Am.Ev) -> {FAm.step.end(b, d, e) == ApprovalsEntry.dspec.end(b, d, e) : FAm.St & String}:
  match b:
    case True{}:
      %ae.next(d) : {FAm.step.reply(e, FAm.D.next(d), Am.dstep(d, e)) == ApprovalsEntry.dk_reply(e, _, Am.dstep(d, e)) : FAm.St & String}
      ae.step_reply(e, FAm.D.next(d), Am.dstep(d, e))
    case False{}:
      {==}

def ae.run(+d: Am.D, r: Wr.Dec<Am.Ev>) -> {FAm.step.ev(d, r) == ApprovalsEntry.dspec.run(d, r) : FAm.St & String}:
  match r:
    case Wr.Got{e, s}:
      ae.end(Wr.end(s), d, e)
    case Wr.Bad{}:
      {==}

# a live desk's step is the spec's on every input
def ae.exact(+d: Am.D, +s: String) -> {FAm.step(FAm.Live{d}, s) == ApprovalsEntry.dspec(d, s) : FAm.St & String}:
  %ae.read(s) : {FAm.step.ev(d, FAm.get_ev(s)) == ApprovalsEntry.dspec.run(d, _) : FAm.St & String}
  ae.run(d, FAm.get_ev(s))

# The reader reads back what Rust writes
# --------------------------------------

def ae.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

def ae.ns(+es: List<&2, Nat>, +rest: String, h: {ApprovalsEntry.ns_fit(es) == True{} : Bool}) -> {Wr.Got{es, rest} == Wr.get_list(~Nat, ~Wr.get_nat, ApprovalsEntry.spell_ns(es, rest)) : Wr.Dec<List<&2, Nat>>}:
  Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, ApprovalsEntry.spell_ns(es, rest)), Wr.Got{es, rest}, Wire.wire_list_round_trip(es, rest, h))

def ae.nat(+k: Nat, +rest: String, h: {LawsBase.wire_fits(k) == True{} : Bool}) -> {Wr.Got{k, rest} == Wr.get_nat(Wr.put_nat(k, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(k, rest)), Wr.Got{k, rest}, Wire.wire_nat_round_trip(k, rest, h))

# the tail of an ask (here, parent) reads back
def ae.rt_hp(+id: String, +es: List<&2, Nat>, h: Am.Here, p: Bool, +rest: String) -> {ApprovalsEntry.read_ask.here(id, es, ApprovalsEntry.read_here(Wr.get_nat(Wr.put_nat(ApprovalsEntry.spell_here(h), Wr.put_bool(p, rest))))) == Wr.Got{Am.EAsk{id, es, h, p}, rest} : Wr.Dec<Am.Ev>}:
  match h:
    case Am.Nobody{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case Am.GatewayOnly{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case Am.Clients{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}

def ae.rt_detach(h: Am.Here, p: Bool, +rest: String) -> {ApprovalsEntry.read_ev(ApprovalsEntry.spell_ev(Am.EDetach{h, p}, rest)) == Wr.Got{Am.EDetach{h, p}, rest} : Wr.Dec<Am.Ev>}:
  match h:
    case Am.Nobody{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case Am.GatewayOnly{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case Am.Clients{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}

def ae.rt_answer(+id: String, y: Bool, +rest: String, h: {LawsBase.wire_fits(String.length(id)) == True{} : Bool}) -> {ApprovalsEntry.read_ev(ApprovalsEntry.spell_ev(Am.EAnswer{id, y}, rest)) == Wr.Got{Am.EAnswer{id, y}, rest} : Wr.Dec<Am.Ev>}:
  match y:
    case True{}:
      %ae.str(id, Wr.put_bool(True{}, rest), h) : {ApprovalsEntry.read_answer.id(_) == Wr.Got{Am.EAnswer{id, True{}}, rest} : Wr.Dec<Am.Ev>}
      {==}
    case False{}:
      %ae.str(id, Wr.put_bool(False{}, rest), h) : {ApprovalsEntry.read_answer.id(_) == Wr.Got{Am.EAnswer{id, False{}}, rest} : Wr.Dec<Am.Ev>}
      {==}

def ae.rt_back(+k: Nat, f: Am.Fate, +rest: String, h: {LawsBase.wire_fits(k) == True{} : Bool}) -> {ApprovalsEntry.read_ev(ApprovalsEntry.spell_ev(Am.EBack{k, f}, rest)) == Wr.Got{Am.EBack{k, f}, rest} : Wr.Dec<Am.Ev>}:
  match f:
    case Am.Runs{}:
      %ae.nat(k, ApprovalsEntry.spell_fate(Am.Runs{}, rest), h) : {ApprovalsEntry.read_back.key(_) == Wr.Got{Am.EBack{k, Am.Runs{}}, rest} : Wr.Dec<Am.Ev>}
      {==}
    case Am.Denied{}:
      %ae.nat(k, ApprovalsEntry.spell_fate(Am.Denied{}, rest), h) : {ApprovalsEntry.read_back.key(_) == Wr.Got{Am.EBack{k, Am.Denied{}}, rest} : Wr.Dec<Am.Ev>}
      {==}
    case Am.Unheard{}:
      %ae.nat(k, ApprovalsEntry.spell_fate(Am.Unheard{}, rest), h) : {ApprovalsEntry.read_back.key(_) == Wr.Got{Am.EBack{k, Am.Unheard{}}, rest} : Wr.Dec<Am.Ev>}
      {==}
    case Am.GatewayRefused{}:
      %ae.nat(k, ApprovalsEntry.spell_fate(Am.GatewayRefused{}, rest), h) : {ApprovalsEntry.read_back.key(_) == Wr.Got{Am.EBack{k, Am.GatewayRefused{}}, rest} : Wr.Dec<Am.Ev>}
      {==}

def ae.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ae.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ae.BD(_, A, Unit)
  Unit{}

def ae.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ae.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ae.absurd({b == True{} : Bool}, h)

# every event Rust spells reads back whole, the rest untouched
def ae.rt(e: Am.Ev, +rest: String, h: {ApprovalsEntry.ev_fits(e) == True{} : Bool}) -> {ApprovalsEntry.read_ev(ApprovalsEntry.spell_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Am.Ev>}:
  match e:
    case Am.EAsk{+id, +es, +hh, +p}:
      +h2 = h
      +tail = Wr.put_nat(ApprovalsEntry.spell_here(hh), Wr.put_bool(p, rest))
      %ae.str(id, ApprovalsEntry.spell_ns(es, tail), ae.and_l(LawsBase.wire_fits(String.length(id)), ApprovalsEntry.ns_fit(es), h2)) : {ApprovalsEntry.read_ask.id(_) == Wr.Got{Am.EAsk{id, es, hh, p}, rest} : Wr.Dec<Am.Ev>}
      %ae.ns(es, tail, ae.and_r(LawsBase.wire_fits(String.length(id)), ApprovalsEntry.ns_fit(es), h2)) : {ApprovalsEntry.read_ask.effs(id, _) == Wr.Got{Am.EAsk{id, es, hh, p}, rest} : Wr.Dec<Am.Ev>}
      ae.rt_hp(id, es, hh, p, rest)
    case Am.EAnswer{+id, y}:
      ae.rt_answer(id, y, rest, h)
    case Am.EDetach{hh, p}:
      ae.rt_detach(hh, p, rest)
    case Am.ECancel{+k}:
      %ae.nat(k, rest, h) : {ApprovalsEntry.read_cancel.key(_) == Wr.Got{Am.ECancel{k}, rest} : Wr.Dec<Am.Ev>}
      {==}
    case Am.EBack{+k, f}:
      ae.rt_back(k, f, rest, h)

# eukhe: the laws of area admission: the stepper, whole
#
# The opens, ops and replies of bend/ffi_admission.bend, spelled and read
# by the spec alone and answered by the controller's spec
# (laws/admission.bend `ads_step`).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../admission.bend as Admission
import ../base.bend as LawsBase

# The stepper, whole: the opens, ops and replies of the grammar (the
# header of bend/ffi_admission.bend) spelled and read with the wire
# primitives of bend/wire.bend and these helpers alone, never with the
# entry's own encoders or decoders, and answered by the spec of the
# controller (ads_step, admission_step_exact). A state the stepper holds
# is the refused state (adw_shut_refuses) or adl_live(st) of a state st
# of the model: an open gives adl_live of the state with no ticket, and
# every step keeps that form (adw_open_exact, adw_step_exact), so every
# reply follows from the spec: a reply that is no error is the controller
# the spec reaches, spelled; every error is one of the entry's texts.

def ads_spell_cls(c: Ad.Cls, rest: String) -> String:
  match c:
    case Ad.Ia{}:
      Wr.put_nat(0n, rest)
    case Ad.Bg{}:
      Wr.put_nat(1n, rest)

def ads_spell_sts(s: Ad.Sts, rest: String) -> String:
  match s:
    case Ad.Queued{}:
      Wr.put_nat(0n, rest)
    case Ad.Granted{}:
      Wr.put_nat(1n, rest)
    case Ad.Held{}:
      Wr.put_nat(2n, rest)
    case Ad.Preempted{}:
      Wr.put_nat(3n, rest)
    case Ad.Ended{}:
      Wr.put_nat(4n, rest)

def ads_spell_lim(l: Ad.Lim, rest: String) -> String:
  match l:
    case Ad.Unl{}:
      Wr.put_nat(0n, rest)
    case Ad.Cap{p}:
      Wr.put_nat(1n, Wr.put_nat(p, rest))

def ads_spell_lv(t: Ad.Lv, rest: String) -> String:
  match t:
    case Ad.Lv{k, c, s}:
      Wr.put_nat(k, ads_spell_cls(c, ads_spell_sts(s, rest)))

# the reply: the limit, providerMaxQueued, the live tickets, the next
# ticket's number
def ads_spell_live(x: Ad.Live, rest: String) -> String:
  match x:
    case Ad.Live{l, q, ts, n}:
      ads_spell_lim(l, Wr.put_nat(q, Wr.put_list(~Ad.Lv, ~ads_spell_lv, ts, Wr.put_nat(n, rest))))

# the op Rust writes for o
def ads_spell_op(o: Ad.Op, rest: String) -> String:
  match o:
    case Ad.Admit{c}:
      Wr.put_nat(0n, ads_spell_cls(c, rest))
    case Ad.Collect{k}:
      Wr.put_nat(1n, Wr.put_nat(k, rest))
    case Ad.Release{k}:
      Wr.put_nat(2n, Wr.put_nat(k, rest))
    case Ad.Depart{k}:
      Wr.put_nat(3n, Wr.put_nat(k, rest))
    case Ad.Limit{l, q}:
      Wr.put_nat(4n, ads_spell_lim(l, Wr.put_nat(q, rest)))

# the open Rust writes: the limit, then providerMaxQueued
def ads_spell_open(l: Ad.Lim, q: Nat, rest: String) -> String:
  ads_spell_lim(l, Wr.put_nat(q, rest))

# tags: 0 interactive, 1 background
def ads_read_cls.tag(n: Nat, s: String) -> Wr.Dec<Ad.Cls>:
  match n:
    case 0n:
      Wr.Got{Ad.Ia{}, s}
    case 1n:
      Wr.Got{Ad.Bg{}, s}
    case 2n+x:
      Wr.Bad{}

def ads_read_cls.go(d: Wr.Dec<Nat>) -> Wr.Dec<Ad.Cls>:
  match d:
    case Wr.Got{n, s}:
      ads_read_cls.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ads_read_cls(s: String) -> Wr.Dec<Ad.Cls>:
  ads_read_cls.go(Wr.get_nat(s))

def ads_read_cap(d: Wr.Dec<Nat>) -> Wr.Dec<Ad.Lim>:
  match d:
    case Wr.Got{p, s}:
      Wr.Got{Ad.Cap{p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# tags: 0 unlimited, 1 a cap of 1 + p slots
def ads_read_lim.tag(n: Nat, s: String) -> Wr.Dec<Ad.Lim>:
  match n:
    case 0n:
      Wr.Got{Ad.Unl{}, s}
    case 1n:
      ads_read_cap(Wr.get_nat(s))
    case 2n+x:
      Wr.Bad{}

def ads_read_lim.go(d: Wr.Dec<Nat>) -> Wr.Dec<Ad.Lim>:
  match d:
    case Wr.Got{n, s}:
      ads_read_lim.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ads_read_lim(s: String) -> Wr.Dec<Ad.Lim>:
  ads_read_lim.go(Wr.get_nat(s))

def ads_read_admit(d: Wr.Dec<Ad.Cls>) -> Wr.Dec<Ad.Op>:
  match d:
    case Wr.Got{c, s}:
      Wr.Got{Ad.Admit{c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ads_read_collect(d: Wr.Dec<Nat>) -> Wr.Dec<Ad.Op>:
  match d:
    case Wr.Got{k, s}:
      Wr.Got{Ad.Collect{k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ads_read_release(d: Wr.Dec<Nat>) -> Wr.Dec<Ad.Op>:
  match d:
    case Wr.Got{k, s}:
      Wr.Got{Ad.Release{k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ads_read_leave(d: Wr.Dec<Nat>) -> Wr.Dec<Ad.Op>:
  match d:
    case Wr.Got{k, s}:
      Wr.Got{Ad.Depart{k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ads_read_limit.q(l: Ad.Lim, d: Wr.Dec<Nat>) -> Wr.Dec<Ad.Op>:
  match d:
    case Wr.Got{q, s}:
      Wr.Got{Ad.Limit{l, q}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ads_read_limit(d: Wr.Dec<Ad.Lim>) -> Wr.Dec<Ad.Op>:
  match d:
    case Wr.Got{l, s}:
      ads_read_limit.q(l, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# tags: 0 admit (a class), 1 collect, 2 release, 3 leave (a ticket),
# 4 limits (a limit, providerMaxQueued)
def ads_read_op.tag(n: Nat, s: String) -> Wr.Dec<Ad.Op>:
  match n:
    case 0n:
      ads_read_admit(ads_read_cls(s))
    case 1n:
      ads_read_collect(Wr.get_nat(s))
    case 2n:
      ads_read_release(Wr.get_nat(s))
    case 3n:
      ads_read_leave(Wr.get_nat(s))
    case 4n:
      ads_read_limit(ads_read_lim(s))
    case 5n+x:
      Wr.Bad{}

def ads_read_op.go(d: Wr.Dec<Nat>) -> Wr.Dec<Ad.Op>:
  match d:
    case Wr.Got{n, s}:
      ads_read_op.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the op at the start of s
def ads_read_op(s: String) -> Wr.Dec<Ad.Op>:
  ads_read_op.go(Wr.get_nat(s))

def ads_read_open.q(l: Ad.Lim, d: Wr.Dec<Nat>) -> Wr.Dec<+Sigma<Ad.Lim, x => Nat>>:
  match d:
    case Wr.Got{q, s}:
      Wr.Got{(l, q), s}
    case Wr.Bad{}:
      Wr.Bad{}

def ads_read_open.go(d: Wr.Dec<Ad.Lim>) -> Wr.Dec<+Sigma<Ad.Lim, x => Nat>>:
  match d:
    case Wr.Got{l, s}:
      ads_read_open.q(l, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# the open at the start of s: the limit, then providerMaxQueued
def ads_read_open(s: String) -> Wr.Dec<+Sigma<Ad.Lim, x => Nat>>:
  ads_read_open.go(ads_read_lim(s))

def ads_open.end(done: Bool, l: Ad.Lim, q: Nat) -> FAd.St & String:
  match done:
    case True{}:
      +x = Admission.adl_live(Ad.St{l, q, Nil{}})
      (FAd.Running{x}, ads_spell_live(x, ""))
    case False{}:
      (FAd.Shut{}, Wr.err("admission: input left over"))

def ads_open.req(lq: +Sigma<Ad.Lim, x => Nat>, done: Bool) -> FAd.St & String:
  (l, q) = lq
  ads_open.end(done, l, q)

def ads_open.go(d: Wr.Dec<+Sigma<Ad.Lim, x => Nat>>) -> FAd.St & String:
  match d:
    case Wr.Got{lq, s}:
      ads_open.req(lq, Wr.end(s))
    case Wr.Bad{}:
      (FAd.Shut{}, Wr.err("admission: malformed open"))

# an open: the controller of the limits s spells with no ticket, and its
# spelling, when nothing is left after them; else the refused state with
# one of the two error texts
def ads_open(s: String) -> FAd.St & String:
  ads_open.go(ads_read_open(s))

def ads_stepper.end(done: Bool, +st: Ad.St, o: Ad.Op) -> FAd.St & String:
  match done:
    case True{}:
      +y = Admission.adl_live(Admission.ads_step(st, o))
      (FAd.Running{y}, ads_spell_live(y, ""))
    case False{}:
      (FAd.Running{Admission.adl_live(st)}, Wr.err("admission: input left over"))

def ads_stepper.go(+st: Ad.St, d: Wr.Dec<Ad.Op>) -> FAd.St & String:
  match d:
    case Wr.Got{o, s}:
      ads_stepper.end(Wr.end(s), st, o)
    case Wr.Bad{}:
      (FAd.Running{Admission.adl_live(st)}, Wr.err("admission: malformed op"))

# a step of the controller of state st: the spec's next state and its
# spelling, for the op s spells when nothing is left after it; else the
# state stays, with one of the two error texts
def ads_stepper(+st: Ad.St, s: String) -> FAd.St & String:
  ads_stepper.go(st, ads_read_op(s))

# LAW adw_open_exact: on every input an open is the spec's: the controller with no ticket of the limits the input spells (read by the spec's reader) and its spelling when nothing is left after them; else the refused state with `E admission: input left over` or `E admission: malformed open`
# EXCLUDES: limits read otherwise than the grammar spells them, a
#   controller opened for input that spells none, a reply spelled otherwise
law adw_open_exact:
  for +s: String
  {FAd.open(s) == ads_open(s) : FAd.St & String}

# LAW adw_step_exact: on every input a step of the controller of any model state is the spec's: the state the spec's op reaches and its spelling, for the op the input spells (read by the spec's reader) when nothing is left after it; else the state stays with `E admission: input left over` or `E admission: malformed op`
# EXCLUDES: an op read otherwise than the grammar spells it, a state other
#   than the spec's, a reply spelled otherwise, a state changed by a bad op
law adw_step_exact:
  for +st: Ad.St
  for +s: String
  {FAd.step(FAd.Running{Admission.adl_live(st)}, s) == ads_stepper(st, s) : FAd.St & String}

# LAW adw_open_spelled: every open Rust writes whose numbers fit the wire, spelled by the spec, opens the controller with no ticket
# EXCLUDES: an open Rust writes refused or read as other limits
law adw_open_spelled:
  for +l: Ad.Lim
  for +q: Nat
  for h: {Bool.and(Admission.adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}
  {FAd.open(ads_spell_open(l, q, "")) == (FAd.Running{Admission.adl_live(Ad.St{l, q, Nil{}})}, ads_spell_live(Admission.adl_live(Ad.St{l, q, Nil{}}), "")) : FAd.St & String}

# LAW adw_step_spelled: every op Rust writes whose numbers fit the wire, spelled by the spec, takes the controller of any model state to the spec's next state
# EXCLUDES: an op Rust writes refused or read as another
law adw_step_spelled:
  for +st: Ad.St
  for +o: Ad.Op
  for h: {Admission.adw_op_fits(o) == True{} : Bool}
  {FAd.step(FAd.Running{Admission.adl_live(st)}, ads_spell_op(o, "")) == (FAd.Running{Admission.adl_live(Admission.ads_step(st, o))}, ads_spell_live(Admission.adl_live(Admission.ads_step(st, o)), "")) : FAd.St & String}

# LAW adw_spec_example (anchor): the spec answers the grammar's bytes: an open of one slot, an interactive admit holds it; a 15-digit limit, an unknown op and input left over are refused
# EXCLUDES: a vacuous adw_open_exact or adw_step_exact (a spec that
#   refuses everything)
law adw_spec_example:
  {ads_open("1,0,1,") == (FAd.Running{Ad.Live{Ad.Cap{0n}, 1n, Nil{}, 0n}}, "1,0,1,0,0,") : FAd.St & String} &
  {ads_stepper(Ad.St{Ad.Cap{0n}, 1n, Nil{}}, "0,0,") == (FAd.Running{Ad.Live{Ad.Cap{0n}, 1n, [Ad.Lv{0n, Ad.Ia{}, Ad.Held{}}], 1n}}, "1,0,1,1,0,0,2,1,") : FAd.St & String} &
  {[Pair.snd(FAd.St, String, ads_open("1,123456789012345,0,")), Pair.snd(FAd.St, String, ads_open("0,0,x")), Pair.snd(FAd.St, String, ads_stepper(Ad.St{Ad.Unl{}, 0n, Nil{}}, "5,")), Pair.snd(FAd.St, String, ads_stepper(Ad.St{Ad.Unl{}, 0n, Nil{}}, "1,0,x"))] == [Wr.err("admission: malformed open"), Wr.err("admission: input left over"), Wr.err("admission: malformed op"), Wr.err("admission: input left over")] : List<&2, String>}

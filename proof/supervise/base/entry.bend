# eukhe: lemmas the proofs of the restart-budget entry share
# (laws/supervise.bend, section "The restart-budget entry, spelled")

import Base
import ../../../bend/ffi_supervise.bend as FS
import ../../../bend/supervise.bend as Su
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/supervise.bend as Supervise
import ../../../laws/wire.bend as Wire
import ../../base/logic/bool.bend as LLogicBool
import ../../base/wire.bend as LWire
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../base.bend as LA

# The entry reads every input as the laws' reader does
# -----------------------------------------------------

def rse.gap(c: Su.Cfg, a: List<&2, Nat>, r: Wr.Dec<Nat>) -> {Supervise.rs_read_req.gap(c, a, r) == FS.get_req.gap(c, a, r) : Wr.Dec<FS.Req>}:
  match r:
    case Wr.Got{g, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rse.ages(c: Su.Cfg, r: Wr.Dec<List<&2, Nat>>) -> {Supervise.rs_read_req.ages(c, r) == FS.get_req.ages(c, r) : Wr.Dec<FS.Req>}:
  match r:
    case Wr.Got{a, s}:
      rse.gap(c, a, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rse.m(k: Nat, w: Nat, b: Nat, r: Wr.Dec<Nat>) -> {Supervise.rs_read_req.m(k, w, b, r) == FS.get_req.cfg(FS.get_cfg.m(k, w, b, r)) : Wr.Dec<FS.Req>}:
  match r:
    case Wr.Got{m, s}:
      rse.ages(Su.Cfg{k, w, b, m}, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def rse.b(k: Nat, w: Nat, r: Wr.Dec<Nat>) -> {Supervise.rs_read_req.b(k, w, r) == FS.get_req.cfg(FS.get_cfg.b(k, w, r)) : Wr.Dec<FS.Req>}:
  match r:
    case Wr.Got{b, s}:
      rse.m(k, w, b, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rse.w(k: Nat, r: Wr.Dec<Nat>) -> {Supervise.rs_read_req.w(k, r) == FS.get_req.cfg(FS.get_cfg.w(k, r)) : Wr.Dec<FS.Req>}:
  match r:
    case Wr.Got{w, s}:
      rse.b(k, w, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rse.k(r: Wr.Dec<Nat>) -> {Supervise.rs_read_req.k(r) == FS.get_req.cfg(FS.get_cfg.k(r)) : Wr.Dec<FS.Req>}:
  match r:
    case Wr.Got{k, s}:
      rse.w(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rse.req(s: String) -> {Supervise.rs_read_req(s) == FS.get_req(s) : Wr.Dec<FS.Req>}:
  rse.k(Wr.get_nat(s))

# The entry answers as the laws spell the model's decision
# --------------------------------------------------------

def rse.verdict(v: Su.Verdict) -> {FS.put_verdict(v, "") == Supervise.rs_spell_verdict(v, "") : String}:
  match v:
    case Su.Relaunch{f, b}:
      {==}
    case Su.GiveUp{f}:
      {==}

def rse.decision(d: Su.Decision) -> {FS.put_reply(FS.decide.of(d), "") == Supervise.rs_spell_decision(d) : String}:
  match d:
    case Su.Decision{+s, +v}:
      %rse.verdict(v) : {Wr.put_list(~Nat, ~Wr.put_nat, Su.St.ages(s), FS.put_verdict(v, "")) == LawsBase.wire_spell_nats(Su.St.ages(s), _) : String}
      Wire.wire_nats_spells(Su.St.ages(s), FS.put_verdict(v, ""))

def rse.answer(q: FS.Req) -> {FS.put_reply(FS.decide(q), "") == Supervise.rs_spell_answer(q) : String}:
  match q:
    case FS.Req{c, +a, g}:
      rse.decision(Su.decide(c, Su.St{a, List.length(&2, Nat, a)}, g))

def rse.fin(b: Bool, q: FS.Req) -> {FS.ffi.fin(b, q) == Supervise.rs_spec.end(b, q) : String}:
  match b:
    case True{}:
      rse.answer(q)
    case False{}:
      {==}

def rse.go(r: Wr.Dec<FS.Req>) -> {FS.ffi.go(r) == Supervise.rs_spec.run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      rse.fin(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

# the entry answers the laws' spec on every input
def rse.exact(+s: String) -> {FS.ffi(s) == Supervise.rs_spec(s) : String}:
  %rse.req(s) : {FS.ffi.go(_) == Supervise.rs_spec(s) : String}
  rse.go(Supervise.rs_read_req(s))

# The reader reads back what Rust writes
# --------------------------------------

def rse.rt_cfg(c: Su.Cfg, +a: List<&2, Nat>, +g: Nat, +rest: String, +fits: {Supervise.rs_req_fits(FS.Req{c, a, g}) == True{} : Bool}) -> {Supervise.rs_read_req(Supervise.rs_spell_req(FS.Req{c, a, g}, rest)) == Wr.Got{FS.Req{c, a, g}, rest} : Wr.Dec<FS.Req>}:
  match c:
    case Su.Cfg{+k, +w, +b, +m}:
      +fk = LawsBase.wire_fits(k)
      +fw = LawsBase.wire_fits(w)
      +fb = LawsBase.wire_fits(b)
      +fm = LawsBase.wire_fits(m)
      +fs = Bool.and(LawsBase.wire_fits(List.length(&2, Nat, a)), LawsBase.wire_nats_fit(a))
      +fg = LawsBase.wire_fits(g)
      +hc = LLogicBool.wr_and_l(Supervise.rs_cfg_fits(Su.Cfg{k, w, b, m}), Bool.and(fs, fg), fits)
      +hag = LLogicBool.wr_and_r(Supervise.rs_cfg_fits(Su.Cfg{k, w, b, m}), Bool.and(fs, fg), fits)
      +hk = LLogicBool.wr_and_l(fk, Bool.and(fw, Bool.and(fb, fm)), hc)
      +hwbm = LLogicBool.wr_and_r(fk, Bool.and(fw, Bool.and(fb, fm)), hc)
      +hw = LLogicBool.wr_and_l(fw, Bool.and(fb, fm), hwbm)
      +hbm = LLogicBool.wr_and_r(fw, Bool.and(fb, fm), hwbm)
      +hb = LLogicBool.wr_and_l(fb, fm, hbm)
      +hm = LLogicBool.wr_and_r(fb, fm, hbm)
      +hs = LLogicBool.wr_and_l(fs, fg, hag)
      +hg = LLogicBool.wr_and_r(fs, fg, hag)
      +g0 = Wr.put_nat(g, rest)
      +l = LawsBase.wire_spell_nats(a, g0)
      %LWire.pw6.nat(k, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(m, l))), hk) : {Supervise.rs_read_req.k(_) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %LWire.pw6.nat(w, Wr.put_nat(b, Wr.put_nat(m, l)), hw) : {Supervise.rs_read_req.w(k, _) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %LWire.pw6.nat(b, Wr.put_nat(m, l), hb) : {Supervise.rs_read_req.b(k, w, _) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %LWire.pw6.nat(m, l, hm) : {Supervise.rs_read_req.m(k, w, b, _) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %Wire.wire_nats_spells(a, g0) : {Supervise.rs_read_req.ages(Su.Cfg{k, w, b, m}, Wr.get_list(~Nat, ~Wr.get_nat, _)) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %LA.ps.ffi_list(a, g0, hs) : {Supervise.rs_read_req.ages(Su.Cfg{k, w, b, m}, _) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %LWire.pw6.nat(g, rest, hg) : {Supervise.rs_read_req.gap(Su.Cfg{k, w, b, m}, a, _) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      {==}

# a request Rust writes reads back, with what follows it
def rse.rt(q: FS.Req, +rest: String, +fits: {Supervise.rs_req_fits(q) == True{} : Bool}) -> {Supervise.rs_read_req(Supervise.rs_spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FS.Req>}:
  match q:
    case FS.Req{c, +a, +g}:
      rse.rt_cfg(c, a, g, rest, fits)

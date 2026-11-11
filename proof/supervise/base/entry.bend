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
import ../../wire/base/spell.bend as LAWireSpell
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../../tools/tools_ffi_reads_only_requests/nats.bend as NL
import ../base.bend as LA

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

# The entry reads back what Rust writes
# -------------------------------------

def rse.rt_cfg(c: Su.Cfg, +a: List<&2, Nat>, +g: Nat, +rest: String, +fits: {Supervise.rs_req_fits(FS.Req{c, a, g}) == True{} : Bool}) -> {FS.get_req(Supervise.rs_spell_req(FS.Req{c, a, g}, rest)) == Wr.Got{FS.Req{c, a, g}, rest} : Wr.Dec<FS.Req>}:
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
      %LWire.pw6.nat(k, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(m, l))), hk) : {FS.get_req.cfg(FS.get_cfg.k(_)) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %LWire.pw6.nat(w, Wr.put_nat(b, Wr.put_nat(m, l)), hw) : {FS.get_req.cfg(FS.get_cfg.w(k, _)) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %LWire.pw6.nat(b, Wr.put_nat(m, l), hb) : {FS.get_req.cfg(FS.get_cfg.b(k, w, _)) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %LWire.pw6.nat(m, l, hm) : {FS.get_req.cfg(FS.get_cfg.m(k, w, b, _)) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %Wire.wire_nats_spells(a, g0) : {FS.get_req.ages(Su.Cfg{k, w, b, m}, Wr.get_list(~Nat, ~Wr.get_nat, _)) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %LA.ps.ffi_list(a, g0, hs) : {FS.get_req.ages(Su.Cfg{k, w, b, m}, _) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      %LWire.pw6.nat(g, rest, hg) : {FS.get_req.gap(Su.Cfg{k, w, b, m}, a, _) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, a, g}, rest} : Wr.Dec<FS.Req>}
      {==}

# a request Rust writes reads back, with what follows it
def rse.rt(q: FS.Req, +rest: String, +fits: {Supervise.rs_req_fits(q) == True{} : Bool}) -> {FS.get_req(Supervise.rs_spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FS.Req>}:
  match q:
    case FS.Req{c, +a, +g}:
      rse.rt_cfg(c, a, g, rest, fits)

# The entry reads only what Rust writes
# -------------------------------------
# Whatever the entry's reader reads is the laws' spelling of a request
# that fits, then its rest: each Nat by wire_nat_exact and
# wire_nat_decoded_fits, the ages by NL.nl.nl, the equation of the input
# so far carried stage by stage.

# a request read: its spelling, then its rest, and it fits
def rse.RQ(s: String, d: Wr.Dec<FS.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Supervise.rs_spell_req(q, r) : String} & {Supervise.rs_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a configuration read: its spelling, then its rest, and it fits
def rse.CF(s: String, d: Wr.Dec<Su.Cfg>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == Supervise.rs_spell_cfg(c, r) : String} & {Supervise.rs_cfg_fits(c) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rse.ro_m(-s: String, +k: Nat, +w: Nat, +b: Nat, +r0: String, pre: {s == Wr.put_nat(k, Wr.put_nat(w, Wr.put_nat(b, r0))) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r0) == d : Wr.Dec<Nat>}) -> rse.CF(s, FS.get_cfg.m(k, w, b, d)):
  match d:
    case Wr.Got{+m, +r}:
      (NL.nl.step(z => Wr.put_nat(k, Wr.put_nat(w, Wr.put_nat(b, z))), s, r0, Wr.put_nat(m, r), pre, Wire.wire_nat_exact(r0, m, r, ed)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(m))), fk, LAWireSpell.ws_and_tt(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(m)), fw, LAWireSpell.ws_and_tt(LawsBase.wire_fits(b), LawsBase.wire_fits(m), fb, Wire.wire_nat_decoded_fits(r0, m, r, ed)))))
    case Wr.Bad{}:
      Unit{}

def rse.ro_b(-s: String, +k: Nat, +w: Nat, +r0: String, pre: {s == Wr.put_nat(k, Wr.put_nat(w, r0)) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r0) == d : Wr.Dec<Nat>}) -> rse.CF(s, FS.get_cfg.b(k, w, d)):
  match d:
    case Wr.Got{+b, +r}:
      rse.ro_m(s, k, w, b, r, NL.nl.step(z => Wr.put_nat(k, Wr.put_nat(w, z)), s, r0, Wr.put_nat(b, r), pre, Wire.wire_nat_exact(r0, b, r, ed)), fk, fw, Wire.wire_nat_decoded_fits(r0, b, r, ed), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def rse.ro_w(-s: String, +k: Nat, +r0: String, pre: {s == Wr.put_nat(k, r0) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r0) == d : Wr.Dec<Nat>}) -> rse.CF(s, FS.get_cfg.w(k, d)):
  match d:
    case Wr.Got{+w, +r}:
      rse.ro_b(s, k, w, r, NL.nl.step(z => Wr.put_nat(k, z), s, r0, Wr.put_nat(w, r), pre, Wire.wire_nat_exact(r0, w, r, ed)), fk, Wire.wire_nat_decoded_fits(r0, w, r, ed), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def rse.ro_k(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rse.CF(s, FS.get_cfg.k(d)):
  match d:
    case Wr.Got{+k, +r}:
      rse.ro_w(s, k, r, Wire.wire_nat_exact(s, k, r, ed), Wire.wire_nat_decoded_fits(s, k, r, ed), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def rse.ro_gap(-s: String, +c: Su.Cfg, +a: List<&2, Nat>, +r0: String, pre: {s == Supervise.rs_spell_cfg(c, LawsBase.wire_spell_nats(a, r0)) : String}, fc: {Supervise.rs_cfg_fits(c) == True{} : Bool}, fa: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, a)), LawsBase.wire_nats_fit(a)) == True{} : Bool}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r0) == d : Wr.Dec<Nat>}) -> rse.RQ(s, FS.get_req.gap(c, a, d)):
  match d:
    case Wr.Got{+g, +r}:
      (NL.nl.step(z => Supervise.rs_spell_cfg(c, LawsBase.wire_spell_nats(a, z)), s, r0, Wr.put_nat(g, r), pre, Wire.wire_nat_exact(r0, g, r, ed)), LAWireSpell.ws_and_tt(Supervise.rs_cfg_fits(c), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, a)), LawsBase.wire_nats_fit(a)), LawsBase.wire_fits(g)), fc, LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, a)), LawsBase.wire_nats_fit(a)), LawsBase.wire_fits(g), fa, Wire.wire_nat_decoded_fits(r0, g, r, ed))))
    case Wr.Bad{}:
      Unit{}

def rse.ro_ages(-s: String, +c: Su.Cfg, -r0: String, pre: {s == Supervise.rs_spell_cfg(c, r0) : String}, fc: {Supervise.rs_cfg_fits(c) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, inv: NL.nl.NL(r0, d)) -> rse.RQ(s, FS.get_req.ages(c, d)):
  match d:
    case Wr.Got{+a, +r1}:
      (e, fa) = inv
      rse.ro_gap(s, c, a, r1, NL.nl.step(z => Supervise.rs_spell_cfg(c, z), s, r0, LawsBase.wire_spell_nats(a, r1), pre, e), fc, fa, Wr.get_nat(r1), {==})
    case Wr.Bad{}:
      Unit{}

def rse.ro_cfg(-s: String, d: Wr.Dec<Su.Cfg>, inv: rse.CF(s, d)) -> rse.RQ(s, FS.get_req.cfg(d)):
  match d:
    case Wr.Got{+c, +r0}:
      (e, fc) = inv
      rse.ro_ages(s, c, r0, e, fc, FS.get_ages(r0), NL.nl.nl(r0))
    case Wr.Bad{}:
      Unit{}

# whatever the entry's reader reads is a request Rust writes, then the
# rest of the input
def rse.ro(+s: String) -> rse.RQ(s, FS.get_req(s)):
  rse.ro_cfg(s, FS.get_cfg(s), rse.ro_k(s, Wr.get_nat(s), {==}))

# The entry is the laws' reader and spec, request by request (rs_spec)
# ---------------------------------------------------------------------

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
